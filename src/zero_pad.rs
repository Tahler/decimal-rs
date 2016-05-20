pub fn zero_str(num_zeros: usize) -> String {
    use std::iter::repeat;
    repeat("0").take(num_zeros).collect::<String>()
}

pub fn pad_left(s: &str, num_zeros: usize) -> String {
    zero_str(num_zeros) + s
}

pub fn pad_right(s: &str, num_zeros: usize) -> String {
    s.to_string() + &zero_str(num_zeros)
}
