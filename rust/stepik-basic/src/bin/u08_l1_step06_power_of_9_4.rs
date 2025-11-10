fn main() {
    let (x, y) = (readn(), readn());
    // 1 -> 9 -> 1
    let d1 = if x % 2 == 0 { 1 } else { 9 };
    // 1 -> 4 -> 6 -> 4
    let d2 = if y == 0 { 1 } else if y % 2 == 0 { 6 } else { 4 };
    println!("Последняя цифра суммы равна {}", (d1 + d2) % 10);
}

fn readn() -> u32 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}
