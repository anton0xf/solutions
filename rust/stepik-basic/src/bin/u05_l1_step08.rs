fn main() {
    std::io::stdin()
        .lines()
        .filter_map(Result::ok)
        .for_each(|s| {
            let x = s.trim().parse::<f64>().expect("parse err") as i32;
            print!("{x}, ")
        });
    println!("0");
}
