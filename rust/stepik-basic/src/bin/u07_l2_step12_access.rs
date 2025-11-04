fn main() {
    let (u, g, o) = (readn(), readn(), readn());
    print_access("User", u);
    print_access("Group", g);
    print_access("Other", o);
}

fn print_access(name: &str, x: u8) {
    println!("{name}{}", match x {
        0 => " (no access).",
        7 => " (full access):",
        _ => ":",
    });
    print_right("read", 4, x);
    print_right("write", 2, x);
    print_right("execute", 1, x);
}

fn print_right(name: &str, y: u8, x: u8) {
    if x & y > 0 {
        println!("    - {name}{}", if x == y {" only"} else {""});
    }
}

fn readn() -> u8 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}
