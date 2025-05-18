// test: $ ( seq 5 ; echo 0 ) | cargo run --bin u05_l2_step06_index
fn main() {
    let lines: Vec<_> = std::io::stdin().lines()
        .filter_map(Result::ok).collect();
    let xs_vec: Vec<_> = lines.iter().take(5)
        .map(|s| s.parse::<f64>().unwrap())
        .collect::<Vec<_>>();
    let xs: [f64; 5] = std::array::from_fn(|i| xs_vec[i]);
    let i: usize = lines.last().unwrap().parse().unwrap();
    println!("{:.2}", xs[i]);
}
