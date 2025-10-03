fn main() {
    let (l, m, n) = (read().trim(), readn(), readn());
    let even = l == "Четный";
    check(even, m);
    check(even, n);
}

fn check(even: bool, n: i64) {
    println!("{n} в город {} вход {}", 
        if even {"Четный"} else {"Нечетный"}, 
        if even == (n % 2 == 0) {"разрешен"} else {"запрещен"});
}

fn read() -> String {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s
}

fn readn() -> i64 {
    read().trim().parse().expect("parse err")
}
