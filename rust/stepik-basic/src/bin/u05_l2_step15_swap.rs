// test: $ printf '%d\n' 0 6 | cargo run --bin u05_l2_step15_swap

fn read_idx() -> usize {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("parse err");
    s.trim().parse().expect("parse err")
}

fn main() {
    let mut arr = [-621.5, 11.1, 2.0, -7.123, 0.125, 0.0, 0.000051789];
    let (i, j) = (read_idx(), read_idx());
    (arr[i], arr[j]) = (arr[j], arr[i]);
    println!("{arr:.9?}");
}
