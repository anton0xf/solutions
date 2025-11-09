// test: $ echo '2134' | cargo run --bin u08_l1_step03_code_compact
// > НОГИ
fn main() {
    let key: Vec<char> = "ОНГИ".chars().collect();
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    println!("{}", s.trim().chars()
             .map(|d| key[d as usize - '1' as usize])
             .collect::<String>());
}
