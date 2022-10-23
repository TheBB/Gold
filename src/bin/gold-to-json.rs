// use gold;

use std::rc::Rc;
use std::collections::HashMap;

fn main() {

    let a = Rc::new("a".to_string());
    let b = Rc::new("a".to_string());

    let mut c: HashMap<Rc<String>, i32> = HashMap::new();
    c.insert(a.clone(), 1);
    println!("{:?}", c.get(&b));
    println!("{:?}", a);
    // c[&a] = 1;


    // gold::parse("320000000000000000000000000000000000000000000000000000000000000").map_or_else(
    //     |err| eprintln!("{}", err),
    //     |node| println!("{:?}", node),
    // );
}
