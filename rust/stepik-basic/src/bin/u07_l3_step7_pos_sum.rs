fn main() {
    let xs = vec![1.0, 3.14, -12.3, -50.0, 100.0, 250.0, -4.0, 7.6];
    let sum: f64 = xs.iter().filter(|x| **x > 0.0).sum();
    println!("{sum:.2}");
}
