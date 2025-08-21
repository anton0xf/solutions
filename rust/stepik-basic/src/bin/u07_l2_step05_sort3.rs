// test: $ printf '%s\n' 3 2 1 | cargo run --bin u07_l2_step05_sort3
fn main() {
    let mut xs: Vec<f64> = std::io::stdin().lines()
        .filter_map(Result::ok)
        .map(|s| s.trim().parse().expect("parse err"))
        .collect();
    if xs[0] > xs[1] {
        xs.swap(0, 1);
    }
    if xs[1] > xs[2] {
        xs.swap(1, 2);
    }
    if xs[0] > xs[1] {
        xs.swap(0, 1);
    }
    let res = xs.iter()
        .map(|x| format!("{x:.1}"))
        .collect::<Vec<_>>()
        .join(", ");
    println!("{res}");
}
