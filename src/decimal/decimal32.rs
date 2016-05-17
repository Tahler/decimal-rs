use std::ops::{Add, Sub, Mul, Div, Neg, Rem};
use std::cmp::PartialEq;
use super::super::num::{Num, Zero, One, Signed};
use super::parse_decimal_error::ParseDecimalError;

const SIGN_MASK: u32 = 0b1_00000_000000_00000000000000000000;
const COMBINATION_MASK: u32 = 0b0_11111_000000_00000000000000000000;

#[derive(Debug, Clone, Copy)]
pub struct Decimal32 {
    data: u32,
}

impl Decimal32 {
    /// Creates and initializes a Decimal32 representation of zero.
    pub fn new() -> Decimal32 {
        Decimal32::zero()
    }
    
    /// Creates and initializes a Decimal32 representation of positive infinity.
    pub fn infinity() -> Decimal32 {
        Decimal32 {
            data: 0b0_11110_000000_00000000000000000000
        }
    }
    
    /// Creates and initializes a Decimal32 representation of negative infinity.    
    pub fn neg_infinity() -> Decimal32 {
        Decimal32 {
            data: 0b1_11110_000000_00000000000000000000
        }
    }
    
    /// Creates and initializes a Decimal32 that is specially encoded as a quiet NaN.
    pub fn quiet_nan() -> Decimal32 {
        Decimal32 {
            data: 0b0_11111_000000_00000000000000000000      
        }
    }

    /// Creates and initializes a Decimal32 that is specially encoded as a signaling NaN.
    pub fn signaling_nan() -> Decimal32 {
        Decimal32 {
            data: 0b0_11111_100000_00000000000000000000      
        }
    }

    /// Copies the data passed into the data in the Decimal32.
    pub fn from_data(data: u32) -> Decimal32 {
        Decimal32 { data: data }
    }

    /// Returns true if the combination field signifies infinity, and false otherwise.    
    pub fn is_infinity(&self) -> bool {
        self.get_combination_field() == 0b11110
    }

    /// Returns true if the combination field signifies infinity and the sign is positive, and false
    /// otherwise.    
    pub fn is_pos_infinity(&self) -> bool {
        self.is_positive() && self.is_infinity()
    }

    /// Returns true if the combination field signifies infinity and the sign is negative, and false
    /// otherwise.    
    pub fn is_neg_infinity(&self) -> bool {
        self.is_negative() && self.is_infinity()
    }
    
    /// Returns true if the combination field signifies NaN, and false otherwise.    
    pub fn is_nan(&self) -> bool {
        self.get_combination_field() == 0b11111
    }

    fn get_sign_field(&self) -> u32 {
        (self.data & SIGN_MASK) >> 31
    }

    fn get_combination_field(&self) -> u32 {
        (self.data & COMBINATION_MASK) >> 26
    }

    fn get_first_two_bits_combination_field(&self) -> u32 {
        let combination_field = self.get_combination_field();
        combination_field >> 3
    }

    fn get_second_two_bits_combination_field(&self) -> u32 {
        let mask = 0b00110;
        let combination_field = self.get_combination_field();
        (combination_field & mask) >> 1
    }

    fn get_normal_exponent(&self) -> u32 {
        let mask: u32 = 0b0_00111_111000_00000000000000000000;
        (self.data & mask) >> 23
    }

    fn get_shifted_exponent(&self) -> u32 {
        let mask: u32 = 0b0_00001_111110_00000000000000000000;
        (self.data & mask) >> 21
    }

    fn get_normal_significand(&self) -> u32 {
        let mask = 0b0_00000_000111_11111111111111111111;
        self.data & mask
    }

    fn get_shifted_significand(&self) -> u32 {
        let implicit_100 = 0b100_0_00000_00000_00000_00000;
        let mask = 0b0_00000_000001_11111111111111111111;
        implicit_100 + (self.data & mask)
    }
}

impl Add<Decimal32> for Decimal32 {
    type Output = Decimal32;

    fn add(self, other: Decimal32) -> Decimal32 {
        let sum;
        let sign = self.get_sign_field();
        if self.is_nan() || other.is_nan() {
            sum = Decimal32::quiet_nan();
        } else if self.is_infinity() {
            if other.is_infinity() {
                sum = Decimal32::infinity();
            }
        } else {
            let exponent;
            let significand;
            if self.get_first_two_bits_combination_field() < 3 {
                exponent = self.get_normal_exponent();
                significand = self.get_normal_significand();
            } else { // self.get_second_two_bits_combination_field() < 3
                exponent = self.get_shifted_exponent();
                significand = self.get_shifted_significand();
            }
            // TODO sum =...
        }
        sum
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
        Decimal32 { data: self.data ^ 1 << 31 }
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
        Decimal32 { data: 0b0_00000_000000_00000000000000000000 }
    }

    fn is_zero(&self) -> bool {
        true
    }
}

impl One for Decimal32 {
    fn one() -> Decimal32 {
        Decimal32 { data: 0b0_00000_000000_00000000000000000001 }
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
        self.get_sign_field() == 0
    }

    /// Note: Zero can be positive or negative.
    fn is_negative(&self) -> bool {
        self.get_sign_field() != 0
    }
}
    