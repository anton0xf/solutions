// test: $ ( seq 5 ; echo 0 ) | cargo run --bin u05_l2_step06_index
fn main() {
    let lines: Vec<_> = std::io::stdin().lines()
        .filter_map(Result::ok).collect();
    let xs: [f64; 5] = lines.iter().take(5)
        .map(|s| s.parse::<f64>().unwrap())
        .collect::<Vec<_>>()
        .try_into().unwrap();
    let i: usize = lines.last().unwrap().parse().unwrap();
    println!("{:.2}", xs[i]);
}
