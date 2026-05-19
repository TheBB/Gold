use gold::pprint::{pprint, pprint_eval, PprintOptions};
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

fn eval_trial(name: String, gold_path: PathBuf, parse_path: PathBuf, eval_path: PathBuf) -> Trial {
    Trial::test(name, move || {
        let source = read(&gold_path)?;
        let expected_parse = read(&parse_path)?;
        let expected_eval = read(&eval_path)?;
        let opts = opts();

        let actual_parse = pprint(&gold::parse(&source), &opts);
        if actual_parse != expected_parse.trim_end_matches('\n') {
            return Err(Failed::from(format!(
                "parse expected:\n{}\n\ngot:\n{}",
                expected_parse.trim_end_matches('\n'),
                actual_parse,
            )));
        }

        let actual_eval = pprint_eval(&gold::eval_file(&gold_path), &opts);
        if actual_eval == expected_eval.trim_end_matches('\n') {
            Ok(())
        } else {
            Err(Failed::from(format!(
                "eval expected:\n{}\n\ngot:\n{}",
                expected_eval.trim_end_matches('\n'),
                actual_eval,
            )))
        }
    })
}

fn main() {
    let args = Arguments::from_args();
    let root = repo_root();
    let testdata = root.join("testdata");

    let mut trials = Vec::new();

    // ── examples ──────────────────────────────────────────────────────────────

    let examples_dir = root.join("examples");
    let example_files = collect_gold_files(&examples_dir);
    trials.push(count_trial("example::fixture_count", example_files.len(), 14));
    for gold_path in example_files {
        let stem = gold_path.file_stem().unwrap().to_str().unwrap().to_string();
        let parse_path = testdata.join("examples").join(format!("{stem}.parse"));
        let eval_path = testdata.join("examples").join(format!("{stem}.eval"));
        trials.push(eval_trial(format!("example::{stem}"), gold_path, parse_path, eval_path));
    }

    // ── eval fixtures ─────────────────────────────────────────────────────────

    let eval_dir = testdata.join("eval");
    let eval_files = collect_gold_files(&eval_dir);
    trials.push(count_trial("eval::fixture_count", eval_files.len(), 455));
    for gold_path in eval_files {
        let rel = gold_path.strip_prefix(&eval_dir).unwrap().with_extension("").to_str().unwrap().to_string();
        let parse_path = gold_path.with_extension("parse");
        let eval_path = gold_path.with_extension("eval");
        trials.push(eval_trial(format!("eval::{rel}"), gold_path, parse_path, eval_path));
    }

    libtest_mimic::run(&args, trials).exit();
}
