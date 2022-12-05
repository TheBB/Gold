use std::path::PathBuf;
use std::process::exit;

use clap::Parser;
use json::{JsonValue, stringify_pretty};

use gold::error::Error;
use gold::eval_file;


#[derive(Parser)]
struct Cli {
    path: PathBuf,
}


fn main() {
    let args = Cli::parse();
    let obj = eval_file(&args.path).and_then(JsonValue::try_from);

    match obj {
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
