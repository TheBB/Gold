use std::path::PathBuf;
use std::process::exit;

use clap::Parser;
use json::{JsonValue, stringify_pretty};

use gold::error::Error;
use gold::{eval_file, eval_raw};


#[derive(Parser)]
struct Cli {
    #[arg(short = 'c')]
    code: Option<String>,
    path: Option<PathBuf>,
}


fn main() {
    let args = Cli::parse();

    let obj = if let Some(path) = args.path {
        eval_file(&path)
    } else if let Some(code) = args.code {
        eval_raw(&code)
    } else {
        eprintln!("Error: no code or path to file given");
        exit(1);
    };

    match obj.and_then(|obj| JsonValue::try_from(&obj)) {
        Ok(val) => println!("{}", stringify_pretty(val, 4)),
        Err(Error { rendered: Some(e), .. }) => {
            eprintln!("{}", e);
            exit(1);
        },
        Err(_) => {
            eprintln!("Error: unknown");
            exit(1);
        }
    }
}
