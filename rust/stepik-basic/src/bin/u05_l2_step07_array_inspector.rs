use std::convert::TryInto;
// test: $ printf '%d\n' 2 1 0 1 2 | cargo run --bin u05_l2_step07_array_inspector
// > 0, 1, 2, 1, 0
fn main() {
    let xs: [i32; 5] = std::io::stdin()
        .lines()
        .map(Result::unwrap)
        .map(|s| s.parse().unwrap())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let res: [i32; 5] = xs.map(|x| xs[x as usize]);
    println!("{}", res.map(|x| x.to_string()).join(", "));
}
