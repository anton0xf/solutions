fn main() {
    let month = readn();
    let season = match month {
        1 | 2 | 12 => "Зима",
        3..=5 => "Весна",
        6..=8 => "Лето",
        9..=11 => "Осень",
        _ => panic!("Unexpected month number: {month}")
    };
    println!("{season}");
}

fn readn() -> u8 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}
