#[regent::bitwise]
struct Timestamp {
    // 1900..=2411
    year: u9,
    // 1..=16
    month: u4,
    // 1..=32
    day: u5,
}

fn main() {
    println!("{:032b}", u32::from(Timestamp::new(123, 2, 18)));
}
