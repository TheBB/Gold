use gold::pprint::{pprint_eval, PprintOptions};
use libtest_mimic::{Arguments, Failed, Trial};
use std::path::{Path, PathBuf};

fn testdata() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("testdata/eval")
}

fn collect_gold_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .collect();
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            collect_gold_files(&path, out);
        } else if path.extension().and_then(|s| s.to_str()) == Some("gold") {
            out.push(path);
        }
    }
}

fn main() {
    let args = Arguments::from_args();
    let testdata = testdata();

    let mut gold_files = Vec::new();
    collect_gold_files(&testdata, &mut gold_files);

    assert_eq!(
        gold_files.len(),
        434,
        "unexpected fixture count — did discovery break?",
    );

    let trials: Vec<Trial> = gold_files
        .into_iter()
        .map(|gold_path| {
            let rel = gold_path
                .strip_prefix(&testdata)
                .unwrap()
                .with_extension("")
                .to_str()
                .unwrap()
                .to_string();
            Trial::test(rel, move || {
                let opts = PprintOptions { show_spans: true, max_str_len: None };
                let eval_path = gold_path.with_extension("eval");
                let source = std::fs::read_to_string(&gold_path)
                    .map_err(|e| Failed::from(e.to_string()))?;
                let expected = std::fs::read_to_string(&eval_path)
                    .map_err(|e| Failed::from(e.to_string()))?
                    .replace("\r\n", "\n");
                let result = gold::eval_raw(&source);
                let actual = pprint_eval(&result, &opts);
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
        })
        .collect();

    libtest_mimic::run(&args, trials).exit();
}
