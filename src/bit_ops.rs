/// Returns the range of bits from index `start` to index `end`.
///
/// `start` and `end` are both inclusive and 0-based from LSB (least significant bit).
pub fn get_bits(bits: u32, start: usize, end: usize) -> u32 {
    // !0 is equal to 0xffffffff
    let range = (end + 1) - start;
    let mask = !(!0 << range);
    (bits >> start) & mask
}

/// Returns the value of the bit at `bit_index`.
///
/// `bit_index` is 0-based from LSB (least significant bit).
pub fn get_bit(bits: u32, bit_index: usize) -> u32 {
    get_bits(bits, bit_index, bit_index)
}

/// Sets the bit at `bit_index` to 1.
///
/// `bit_index` is 0-based from LSB (least significant bit).
pub fn set_bit(bits: u32, bit_index: usize) -> u32 {
    let mask = 1 << bit_index;
    bits | mask
}

/// Sets the bit at `bit_index` to 0.
///
/// `bit_index` is 0-based from LSB (least significant bit).
pub fn clear_bit(bits: u32, bit_index: usize) -> u32 {
    let mask = !(1 << bit_index);
    bits & mask
}

/// Flips the bit at `bit_index` to 0.
///
/// `bit_index` is 0-based from LSB (least significant bit).
pub fn toggle_bit(bits: u32, bit_index: usize) -> u32 {
    let mask = 1 << bit_index;
    bits ^ mask
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_bits() {
        assert_eq!(0xff, get_bits(0xff000000, 24, 31));
        assert_eq!(0b_101, get_bits(0b110101, 0, 2));

        let bit_32 = 0b1_00111010_01101000110011111000000;
        assert_eq!(0b1, get_bits(bit_32, 31, 31));
        assert_eq!(0b1, get_bit(bit_32, 31));
        assert_eq!(0b00111010, get_bits(bit_32, 23, 30));
        assert_eq!(0b01101000110011111000000, get_bits(bit_32, 0, 22));

        let bit_32 = 0b0_01011110_11001011011100110101010;
        assert_eq!(0b0, get_bits(bit_32, 31, 31));
        assert_eq!(0b0, get_bit(bit_32, 31));
        assert_eq!(0b01011110, get_bits(bit_32, 23, 30));
        assert_eq!(0b11001011011100110101010, get_bits(bit_32, 0, 22));
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
