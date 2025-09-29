// test it by: $ echo '12434' | cargo run --bin u07_l2_step07_digits
// > 44321
fn main() {
    let n = read();
    let mut ds = digits(n);
    ds.sort();
    ds.reverse();
    println!("{}", from_digits(ds));
}

fn read() -> i64 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}

fn digits(n: i64) -> Vec<i8> {
    if n <= 0 {
        return vec![0];
    }
    let mut v: Vec<i8> = Vec::new();
    let mut m = n;
    while m > 0 {
        v.push((m % 10) as i8);
        m /= 10;
    }
    v.reverse();
    v
}

fn from_digits(v: Vec<i8>) -> i64 {
    let mut n: i64 = 0;
    for d in v {
        n = n * 10 + (d as i64);
    }
    n
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_digits() {
        assert_eq!(digits(123), vec![1, 2, 3]);
    }

    #[test]
    fn test_from_digits() {
        assert_eq!(from_digits(vec![1, 2, 3]), 123);
    }
}
