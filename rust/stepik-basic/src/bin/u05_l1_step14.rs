fn main() {
    let xs = [3.0, 0.1, 0.04, 0.001, 0.0005, 0.00009, 0.000002, 0.0000006];
    let sum = xs.iter().fold(0.0, |acc, x| acc + x);
    println!("{sum:.7}");
}
