use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        gold::parse(args[1].as_str()).map_or_else(
            |err| eprintln!("{:#?}", err),
            |node| println!("{:#?}", node),
        )
    } else {
        eprintln!("Error: provide one argument");
    }
}
