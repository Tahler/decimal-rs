const N_DIGITS: usize = 128;
const N_BYTES: usize = N_DIGITS / 8;

#[derive(Debug, Clone, Copy)]
struct Decimal {
    digits: [u8; N_BYTES],
    exp: u8,
    neg: bool,
}

impl Decimal {
    pub fn new() -> Decimal {
        Decimal {
            digits: [0; N_BYTES],
            exp: 0,
            neg: false,
        }
    }
}
