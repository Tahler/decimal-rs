/// `start` and `end` are 0-based from LSB (least significant bit).
/// `start` is inclusive and `end` is exclusive.
pub fn get_bits(bits: u32, start: usize, end: usize) -> u32 {
    // !0 is equal to 0xffffffff
    let mask = !(!0 << (end - start + 1));
    (bits >> start) & mask
}

pub fn set_bit(bits: u32, bit_index: usize) -> u32 {
    let mask = 1 << bit_index;
    bits | mask
}

pub fn clear_bit(bits: u32, bit_index: usize) -> u32 {
    let mask = !(1 << bit_index);
    bits & mask
}

pub fn toggle_bit(bits: u32, bit_index: usize) -> u32 {
    let mask = 1 << bit_index;
    bits ^ mask
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_bits() {
        assert_eq!(0xff, get_bits(0xff000000, 24, 32));
    }

    #[test]
    fn test_set_bit() {
        assert_eq!(0b1011, set_bit(0b1010, 0));
        assert_eq!(0b1011, set_bit(0b1011, 0));
        assert_eq!(0b1010, set_bit(0b0010, 3));
    }

    #[test]
    fn test_clear_bit() {
        assert_eq!(0b1010, clear_bit(0b1011, 0));
        assert_eq!(0b1010, clear_bit(0b1010, 0));
        assert_eq!(0b0010, clear_bit(0b1010, 3));
    }

    #[test]
    fn test_toggle_bit() {
        assert_eq!(0b1011, toggle_bit(0b1010, 0));
        assert_eq!(0b1010, toggle_bit(0b1011, 0));
        assert_eq!(0b1010, toggle_bit(0b0010, 3));
    }
}
