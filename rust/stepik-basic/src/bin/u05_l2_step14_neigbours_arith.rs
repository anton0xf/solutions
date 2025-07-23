// test: $ echo '1' | cargo run --bin u05_l2_step14_neigbours_arith

fn main() {
    let arr = [-5, 1, 8, 2, 30, 4000, 500000];
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    let i: usize = s.trim().parse().expect("parse err");
    let (x, y) = (arr[i - 1], arr[i + 1]);
    println!("{}", x + y);
    println!("{}", x - y);
    println!("{}", x * y);
}
