// test: $ echo 10 | cargo run --bin u06_l1_step06_km_conv
fn readf() -> f64 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}

fn main() {
    let m = [
        (0.621371, "миль"),
        (1093.61, "ярдов"),
        (3280.84, "футов"),
        (39370.1, "дюймов"),
    ];
    let x = readf();
    for (c, name) in m {
        let y = x * c;
        println!("{x:.3} км = {y:.3} {name}");
    }
}
