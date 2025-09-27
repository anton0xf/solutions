fn main() {
    let ns: [i64;4] = [1, 2, 5, 10];
    let n = read();
    if ns.contains(&n) {
        println!("Принята монета номинала {n}");
    } else {
        println!("Монеты такого номинала не принимаются");
    }
}

fn read() -> i64 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}
