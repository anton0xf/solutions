// test: $ echo 3665 | cargo run --bin u06_l1_step07_sec
fn main() {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    let n: u64 = s.trim().parse().expect("parse err");
    let s = n % 60;
    let total_m = n / 60;
    let m = total_m % 60;
    let h = total_m / 60;
    println!("{n} сек = {h} час {m} минут {s} секунд");
}
