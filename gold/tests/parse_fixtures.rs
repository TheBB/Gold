use gold::pprint::{pprint, PprintOptions};
use libtest_mimic::{Arguments, Failed, Trial};
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_owned()
}

fn collect_gold_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    collect_rec(dir, &mut out);
    out
}

fn collect_rec(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .collect();
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            collect_rec(&path, out);
        } else if path.extension().and_then(|s| s.to_str()) == Some("gold") {
            out.push(path);
        }
    }
}

fn opts() -> PprintOptions {
    PprintOptions { show_spans: true, max_str_len: None }
}

fn read(path: &Path) -> Result<String, Failed> {
    std::fs::read_to_string(path)
        .map(|s| s.replace("\r\n", "\n"))
        .map_err(|e| Failed::from(e.to_string()))
}

fn count_trial(name: &'static str, actual: usize, expected: usize) -> Trial {
    Trial::test(name, move || {
        if actual == expected {
            Ok(())
        } else {
            Err(Failed::from(format!(
                "unexpected fixture count — did discovery break? expected {expected}, got {actual}",
            )))
        }
    })
}

fn parse_trial(name: String, gold_path: PathBuf, parse_path: PathBuf) -> Trial {
    Trial::test(name, move || {
        let source = read(&gold_path)?;
        let expected = read(&parse_path)?;
        let opts = opts();

        let actual = pprint(&gold::parse(&source), &opts);
        if actual == expected.trim_end_matches('\n') {
            Ok(())
        } else {
            Err(Failed::from(format!(
                "expected:\n{}\n\ngot:\n{}",
                expected.trim_end_matches('\n'),
                actual,
            )))
        }
    })
}

fn main() {
    let root = repo_root();
    let parse_dir = root.join("testdata").join("parse");

    let gold_files = collect_gold_files(&parse_dir);
    let mut trials = Vec::new();

    trials.push(count_trial("parse::fixture_count", gold_files.len(), 159));

    for gold_path in gold_files {
        let rel = gold_path
            .strip_prefix(&parse_dir)
            .unwrap()
            .with_extension("")
            .to_str()
            .unwrap()
            .to_string();
        let parse_path = gold_path.with_extension("parse");
        trials.push(parse_trial(format!("parse::{rel}"), gold_path, parse_path));
    }

    libtest_mimic::run(&Arguments::from_args(), trials).exit();
}
