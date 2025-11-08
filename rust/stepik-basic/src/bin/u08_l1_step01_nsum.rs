fn main() {
    println!("{}", nsum(readn()));
}

fn nsum(n: i64) -> i64 {
    let sig = n.signum();
    let mut m = n.abs();
    let mut sum = 0;
    while m > 0 {
        if m <= 9 {
            return sum + sig * m
        }
        sum += m % 10;
        m /= 10;
    }
    sum
}

fn readn() -> i64 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pos() {
        assert_eq!(nsum(123), 6);
    }

    #[test]
    fn test_neg() {
        assert_eq!(nsum(-123), 4);
    }
}
