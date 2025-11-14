fn main() {
    let (d, m, y) = (readn(), readn(), readn());
    if valid(d, m, y) {
        println!("Дата корректна!");
    } else {
        println!("Дата некорректна!");
    }
}

fn valid(d: u16, m: u16, y: u16) -> bool {
    if d == 0 || y == 0 || y > 2024 {
        return false;
    }
    let max_day = match m {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        2 if leap_year(y) => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => return false
    };
    d <= max_day
}

fn leap_year(y: u16) -> bool {
    y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
}

fn readn() -> u16 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}
