fn main() {
    let (coin, banknote) = (read(), read());
    if [1, 2, 5, 10].contains(&coin) {
        println!("Принята монета номинала {coin}");
    } else {
        println!("Монеты такого номинала не принимаются");
    }

    if [5, 10, 50, 100, 200, 500, 1000, 2000, 5000].contains(&banknote) {
        println!("Принята купюра номинала {banknote}");
    } else {
        println!("Купюры такого номинала не принимаются");
    }
}

fn read() -> i64 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}
