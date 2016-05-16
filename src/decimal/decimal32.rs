use std::ops::{Add, Sub, Mul, Div, Neg, Rem};
use std::cmp::{PartialEq};
use super::super::num::{Num, Zero, One, Signed};
use super::parse_decimal_error::ParseDecimalError;

const ZERO: u32 = 0b0_00000_000000_00000000000000000000;
const SIGN_MASK: u32 = 0b1_00000_000000_00000000000000000000;
const COMBINATION_MASK: u32 = 0b0_11111_000000_00000000000000000000;
const EXPONENT_MASK: u32 = 0b0_00000_111111_00000000000000000000;
const COEFFICIENT_CONTINUATION_MASK: u32 = 0b0_00000_000000_11111111111111111111;

#[derive(Debug, Clone, Copy)]
pub struct Decimal32 {
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

impl Sub<Decimal32> for Decimal32 {
    type Output = Decimal32;   
    
    fn sub(self, other: Decimal32) -> Decimal32 {
        self // TODO
    }
}

impl Mul<Decimal32> for Decimal32 {
    type Output = Decimal32;
    
    fn mul(self, other: Decimal32) -> Decimal32 {
        self // TODO
    }
}

impl Div<Decimal32> for Decimal32 {
    type Output = Decimal32;
    
    fn div(self, other: Decimal32) -> Decimal32 {
        self // TODO
    }
}

impl Neg for Decimal32 {
    type Output = Decimal32;
    
    fn neg(self) -> Decimal32 {
        Decimal32 {
            data: self.data ^ 1 << 31
        }
    }    
}

impl Rem<Decimal32> for Decimal32 {
    type Output = Decimal32;
    
    fn rem(self, other: Decimal32) -> Decimal32 {
        self // TODO
    }
}

impl PartialEq for Decimal32 {
    fn eq(&self, other: &Decimal32) -> bool {
        true // TODO        
    }
}

impl Num for Decimal32 {
    type FromStrRadixErr = ParseDecimalError;
    
    fn from_str_radix(s: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        Ok(Decimal32::zero()) // TODO
    }
}

impl Zero for Decimal32 {
    fn zero() -> Decimal32 {
        Decimal32 { data: ZERO }
    }

    fn is_zero(&self) -> bool {
        true
    }
}

impl One for Decimal32 {
    fn one() -> Decimal32 {
        Decimal32 { data: ZERO } // TODO
    }
}

impl Signed for Decimal32 {
    fn abs(&self) -> Decimal32 {
        Decimal32 { data: self.data & (!SIGN_MASK) }        
    }
    
    fn abs_sub(&self, other: &Decimal32) -> Decimal32 {
        // TODO
        // The positive difference of two numbers.
        // Returns zero if the number is less than or equal to other, otherwise the difference between self and other is returned.
        *self
    }
    
    fn signum(&self) -> Decimal32 {
        // TODO
        // Returns the sign of the number.
        // For f32 and f64:
        // 1.0 if the number is positive, +0.0 or INFINITY
        // -1.0 if the number is negative, -0.0 or NEG_INFINITY
        // NaN if the number is NaN
        *self
    }

    /// Note: Zero can be positive or negative.    
    fn is_positive(&self) -> bool {
        self.data & SIGN_MASK == 0
    }
    
    /// Note: Zero can be positive or negative.
    fn is_negative(&self) -> bool {
        self.data & ZERO != 0
    }
}
    