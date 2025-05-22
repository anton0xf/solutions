// test it with: $ printf "%s\n" a b c d e | cargo run --bin u05_l1_step07
fn main() {
    let ls: Vec<_> = std::io::stdin().lines()
        .filter_map(|line| line.ok())
        .map(|line| line + "\n")
        .collect();
    let tup = (ls[0].as_str(), ls[1].as_str(), ls[2].as_str(), ls[3].as_str(), ls.get(4).unwrap());
    println!("{tup:?}");
}
