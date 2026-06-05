use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        let result = gold::parse(args[1].as_str());
        for err in &result.errors {
            eprintln!("{:#?}", err);
        }
        println!("{:#?}", result.tree);
    } else {
        eprintln!("Error: provide one argument");
    }
}
