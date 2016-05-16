use std::ops::{Add, Sub, Mul, Div};
use super::num::{Zero, One, Signed};

// 0b0_00000_000000_00000000000000000000
const SIGN_MASK: u32 = 0b1_00000_000000_00000000000000000000;
const COMBINATION_MASK: u32 = 0b0_11111_000000_00000000000000000000;
const EXPONENT_MASK: u32 = 0b0_00000_111111_00000000000000000000;
const COEFFICIENT_CONTINUATION_MASK: u32 = 0b0_00000_000000_11111111111111111111;

#[derive(Debug, Clone, Copy)]
struct Decimal32 {
    data: u32,
}

impl Decimal32 {
    /// Creates and initializes a Decimal32 representation of zero.
    pub fn new() -> Decimal32 {
        Decimal32::zero()
    }
}

impl Add<Decimal32> for Decimal32 {
    type Output = Decimal32;

    fn add(self, other: Decimal32) -> Decimal32 {
        self // TODO
    }
}

impl Mul<Decimal32> for Decimal32 {
    type Output = Decimal32;
    
    fn mul(self, other: Decimal32) -> Decimal32 {
        self // TODO
    }
}

impl Zero for Decimal32 {
    fn zero() -> Decimal32 {
        Decimal32 { data: 0b0_00000_000000_00000000000000000000 }
    }

    fn is_zero(&self) -> bool {
        true
    }
}

impl One for Decimal32 {
    fn one() -> Decimal32 {
        Decimal32 { data: 0b0_00000_000000_00000000000000000000 } // TODO
    }
}

// impl Signed for Decimal32 {
//     fn abs(&self) -> Decimal32 {
//         Decimal32 { data: self.data & 0b0_11111_111111_11111111111111111111 }        
//     }
    
//     fn abs_sub(&self) -> Decimal32 {
//         // TODO
//         // The positive difference of two numbers.
//         // Returns zero if the number is less than or equal to other, otherwise the difference between self and other is returned.
//         self
//     }
    
//     fn signum(&self) -> Decimal32 {
//         // TODO
//         // Returns the sign of the number.
//         // For f32 and f64:
//         // 1.0 if the number is positive, +0.0 or INFINITY
//         // -1.0 if the number is negative, -0.0 or NEG_INFINITY
//         // NaN if the number is NaN
//         self
//     }
    
//     fn is_positive(&self) -> bool {
//         self.data & (1 << 32) != 0
//     }
// }
