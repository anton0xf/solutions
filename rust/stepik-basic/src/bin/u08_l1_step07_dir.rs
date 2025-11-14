fn main() {
    let dirs = vec!("Север", "Восток", "Юг", "Запад"); // clockwise
    let (dir, cmd) = (read(), read());
    let id = dirs.iter().position(|&d| d == dir).expect("not found");
    let res = match cmd.as_str() {
        "0" => dir.as_str(),
        "1" => dirs[(id - 1) % 4],
        "2" => dirs[(id + 1) % 4],
        _ => panic!("unexpected command")
    };
    println!("Направление лунохода после выполнения команды: {res}");
}

fn read() -> String {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().to_string()
}
