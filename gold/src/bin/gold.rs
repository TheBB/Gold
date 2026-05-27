use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;
use std::process;

use clap::{Parser, Subcommand};

use gold::pprint::{pprint, PprintOptions};

#[derive(Parser)]
#[command(name = "gold")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Parse a Gold source file and print the parse tree
    Parse {
        /// Source file (reads from stdin if omitted)
        file: Option<PathBuf>,

        /// Include span offsets in the output
        #[arg(long)]
        spans: bool,

        /// Truncate strings longer than N characters
        #[arg(long, value_name = "N")]
        max_str_len: Option<usize>,
    },
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Command::Parse { file, spans, max_str_len } => {
            let source = match file {
                Some(path) => fs::read_to_string(&path).unwrap_or_else(|e| {
                    eprintln!("Error reading {}: {e}", path.display());
                    process::exit(1);
                }),
                None => {
                    let mut buf = String::new();
                    io::stdin().read_to_string(&mut buf).unwrap_or_else(|e| {
                        eprintln!("Error reading stdin: {e}");
                        process::exit(1);
                    });
                    buf
                }
            };

            let result = gold::parse(&source);
            let opts = PprintOptions { show_spans: spans, max_str_len };
            println!("{}", pprint(&result, &opts));
        }
    }
}
