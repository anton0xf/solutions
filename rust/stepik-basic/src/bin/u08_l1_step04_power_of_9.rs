fn main() {
    let mults: Vec<u8> = (0..=9).map(|d| d * 9 % 10).collect();
    let n = readn();
    let mut d = 9u8;
    for _ in 1..n {
        d = mults[d as usize];
    }
    println!("Последняя цифра 9 в степени {n} равна {d}");
}

fn readn() -> u8 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}
