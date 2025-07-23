// test: $ printf '%s\n' 1 -10 | cargo run --bin u05_l2_step08_ch_arr
// > [0, -10, 0, 0, 0, 0, 0, 0, 0, 0]
fn main() {
    let i_x: Vec<i32> = std::io::stdin()
        .lines()
        .map(|s| s.unwrap().trim().parse().unwrap())
        .collect();
    match i_x[..] {
        [i, x] => {
            let mut xs = [0; 10];
            xs[i as usize] = x;
            println!("{xs:?}");
        }
        _ => println!("error"),
    }
}
