fn main() {
    println!("{}", decode(readn()));
}

const KEY: [char; 4] = ['О', 'Н', 'Г', 'И'];

fn decode(n: u64) -> String {
    let mut m = n;
    let mut v: Vec<char> = Vec::new();
    while m > 0 {
        v.push(KEY[(m % 10 - 1) as usize]);
        m /= 10;
    }
    v.into_iter().rev().collect()
}

fn readn() -> u64 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}
