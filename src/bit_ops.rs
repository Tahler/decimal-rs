pub fn toggle_bit(num: u32, bit_index: usize) -> u32 {
    num ^ (1 << bit_index)
}
