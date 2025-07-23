use std::io;

fn main() {
    let out = io::stdin()
        .lines()
        .filter_map(|line| line.ok())
        .collect::<Vec<String>>()
        .join("");
    println!("{out}");
}
