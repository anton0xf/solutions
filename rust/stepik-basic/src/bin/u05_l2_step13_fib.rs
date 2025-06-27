fn main() {
    let arr = [0, 1, 1, 2, 3, 5];
    let res = arr.iter()
        .map(i32::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    println!("{res}");
}
