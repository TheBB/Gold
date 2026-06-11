use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;
use std::process;

use clap::{Parser, Subcommand};
use json::{stringify_pretty, JsonValue};

use gold::pprint::{pprint, pprint_eval, PprintOptions};
use gold::{eval_file, eval_raw, Res, Object};

#[derive(Parser)]
#[command(name = "gold")]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,

    /// Gold file to convert to JSON (when no subcommand is given)
    #[arg(conflicts_with = "code")]
    file: Option<PathBuf>,

    /// Gold source code to evaluate
    #[arg(short = 'c', conflicts_with = "file")]
    code: Option<String>,
}

#[derive(Subcommand)]
enum Command {
    /// Parse a Gold source file and print the parse tree
    Parse {
        /// Source file (reads from stdin if omitted)
        #[arg(conflicts_with = "code")]
        file: Option<PathBuf>,

        /// Gold source code to parse
        #[arg(short = 'c', conflicts_with = "file")]
        code: Option<String>,

        /// Include span offsets in the output
        #[arg(long)]
        spans: bool,

        /// Truncate strings longer than N characters
        #[arg(long, value_name = "N")]
        max_str_len: Option<usize>,
    },

    /// Evaluate a Gold source file and print the result tree
    Run {
        /// Source file (reads from stdin if omitted)
        #[arg(conflicts_with = "code")]
        file: Option<PathBuf>,

        /// Gold source code to evaluate
        #[arg(short = 'c', conflicts_with = "file")]
        code: Option<String>,

        /// Include span offsets in the output
        #[arg(long)]
        spans: bool,
    },
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Some(Command::Parse { file, code, spans, max_str_len }) => {
            let source = get_source(code, file);
            let result = gold::parse(&source);
            let opts = PprintOptions { show_spans: spans, max_str_len };
            println!("{}", pprint(&result, &opts));
        }

        Some(Command::Run { file, code, spans }) => {
            let result = eval_source(code, file);
            let opts = PprintOptions { show_spans: spans, max_str_len: None };
            println!("{}", pprint_eval(&result, &opts));
        }

        None => {
            match eval_source(cli.code, cli.file).and_then(JsonValue::try_from) {
                Ok(val) => println!("{}", stringify_pretty(val, 4)),
                Err(error) => match error.rendered() {
                    Some(e) => {
                        eprintln!("{}", e);
                        process::exit(1);
                    }
                    _ => {
                        eprintln!("Error: {:?}", error);
                        process::exit(1);
                    }
                },
            }
        }
    }
}

fn get_source(code: Option<String>, file: Option<PathBuf>) -> String {
    if let Some(c) = code {
        return c;
    }
    match file {
        Some(path) => fs::read_to_string(&path).unwrap_or_else(|e| {
            eprintln!("Error reading {}: {e}", path.display());
            process::exit(1);
        }),
        None => read_stdin(),
    }
}

fn eval_source(code: Option<String>, file: Option<PathBuf>) -> Res<Object> {
    if let Some(c) = code {
        eval_raw(&c)
    } else if let Some(ref path) = file {
        eval_file(path)
    } else {
        eval_raw(&read_stdin())
    }
}

fn read_stdin() -> String {
    let mut buf = String::new();
    io::stdin().read_to_string(&mut buf).unwrap_or_else(|e| {
        eprintln!("Error reading stdin: {e}");
        process::exit(1);
    });
    buf
}
