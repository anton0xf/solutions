// test: $ echo 21 | cargo run --bin u06_l1_step04_sum_digits

fn main() {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    let n: u16 = s.trim().parse().expect("parse err");
    let sum: u16 = digits(n).iter().sum();
    println!("{sum}");
}

const BASE: u16 = 10;

fn digits(n: u16) -> Vec<u16> {
    if n == 0 {
        vec![0]
    } else if n < BASE {
        vec![n]
    } else {
        let mut res = digits(n / BASE);
        res.push(n % BASE);
        res
    }
}
