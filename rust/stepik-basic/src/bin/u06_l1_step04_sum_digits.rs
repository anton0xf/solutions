// test: $ echo 21 | cargo run --bin u06_l1_step04_sum_digits

fn main() {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    let n: u16 = s.trim().parse().expect("parse err");
    println!("{}", sum_digits(n));
}

fn sum_digits(n: u16) -> u16 {
    if n < 10 { n } else { sum_digits(n / 10) + n % 10 }
}
