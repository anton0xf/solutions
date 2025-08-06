// test: $ echo 1234 | cargo run --bin u06_l1_step04_sum_digits

fn main() {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    let n: u16 = s.trim().parse().expect("parse err");
    let ds = digits(n);
    println!("Последняя цифра: {}", ds[3]);
    println!("Третья цифра: {}", ds[2]);
    println!("Вторая цифра: {}", ds[1]);
    println!("Первая цифра: {}", ds[0]);
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
