fn main() {
    let n = readn();
    let d = if n % 2 == 0 { 1 } else { 9 } ;
    println!("Последняя цифра 9 в степени {n} равна {d}");
}

fn readn() -> u8 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}
