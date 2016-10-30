pub fn num_digits(num: i32, radix: u32) -> u32 {
    let num: f32 = num as f32;
    let radix: f32 = radix as f32;
    let digits: f32 = num.abs().log(radix);
    digits as u32 + 1
}

pub fn num_decimal_digits(num: i32) -> u32 {
    num_digits(num, 10)
}

/// Rounds away from zero.
///
/// `remainder` must be between -1.0 and 1.0
pub fn round_away(num: u32, remainder: f32) -> u32 {
    if remainder <= -0.5 {
        num - 1
    } else if remainder >= 0.5 {
        num + 1
    } else {
        num
    }
}

#[cfg(test)]
mod tests {
    use super::num_digits;

    #[test]
    fn test_num_digits() {
        assert_eq!(1, num_digits(0, 10));
        assert_eq!(1, num_digits(1, 10));
        assert_eq!(1, num_digits(9, 10));
        assert_eq!(3, num_digits(999, 10));
        assert_eq!(4, num_digits(1000, 10));

        assert_eq!(3, num_digits(5, 2));

        assert_eq!(6, num_digits(0b101101, 2));
    }

    #[test]
    fn test_num_decimal_digits() {
        assert_eq!(1, num_digits(1, 10));
        assert_eq!(1, num_digits(9, 10));
        assert_eq!(1, num_digits(0, 10));
        assert_eq!(1, num_digits(-1, 10));
        assert_eq!(3, num_digits(-100, 10));
        assert_eq!(3, num_digits(100, 10));
        assert_eq!(3, num_digits(199, 10));
        assert_eq!(3, num_digits(999, 10));
        assert_eq!(4, num_digits(1000, 10));
    }
}
