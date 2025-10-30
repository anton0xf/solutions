fn main() {
    let (age, sys, dia) = (readn(), readn(), readn());
    let ((sys_min, sys_max), (dia_min, dia_max)) =
        if 18 <= age && age <= 39 {
            ((90, 139), (60, 89))
        } else if 40 <= age && age <= 59 {
            ((91, 149), (61, 91))
        } else if age >= 60 {
            ((91, 159),	(61, 91))
        } else {
            panic!("unexpected age {age}");
        };
    if sys_min <= sys && sys <= sys_max &&
        dia_min <= dia && dia <= dia_max {
            println!("Систолическое и Диастолическое АД в норме");
        } else {
            check_range("Систолическое", sys, sys_min, sys_max);
            check_range("Диастолическое", dia, dia_min, dia_max);
        }
}

fn check_range(name: &str, x: u8, min: u8, max: u8) {
    if min <= x && x <= max {
        println!("{name} АД в норме");
    } else {
        let s = if x < min {
            format!("ниже нормы на {}", min - x)
        } else {
            format!("выше нормы на {}", x - max)
        };
        println!("{name} АД {x} {s}");
    }

}

fn readn() -> u8 {
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).expect("read err");
    s.trim().parse().expect("parse err")
}
