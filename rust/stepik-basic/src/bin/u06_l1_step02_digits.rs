// test: $ echo 21 | cargo run --bin u06_l1_step02_digits

fn main() {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    let n: u8 = s.trim().parse().expect("parse err");
    println!("{}\n{}", n / 10, n % 10);
}
