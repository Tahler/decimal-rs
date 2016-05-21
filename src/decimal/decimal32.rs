use std::ops::{Add, Sub, Mul, Div, Neg, Rem};
use std::cmp::PartialEq;
use std::fmt;
use std::default::Default;
use super::super::num::{Num, Zero, One, Signed};
use super::parse_decimal_error::ParseDecimalError;

const NUM_DIGITS: u32 = 7;

const SIGN_MASK: u32 = 0b1_00000_000000_00000000000000000000;
const COMBINATION_MASK: u32 = 0b0_11111_000000_00000000000000000000;

/// Represents a 32-bit decimal number according to the [IEEE 754-2008 standard]
/// (https://en.wikipedia.org/wiki/Decimal32_floating-point_format).
///
/// Decimal32 supports 7 decimal digits of significand and an exponent range of −95 to +96, i.e.
/// ±0.000000×10^−95 to ±9.999999×10^96. (Equivalently, ±0000000×10^−101 to ±9999999×10^90.)
#[derive(Debug, Clone, Copy)]
pub struct Decimal32 {
    data: u32,
}

impl Decimal32 {
    /// Creates and initializes a Decimal32 representation of zero.
    pub fn new() -> Decimal32 {
        Decimal32::zero()
    }

    /// Creates and initialize a Decimal32 from its significant parts: the sign, exponent, and
    /// significand, respectively.
    ///
    /// Returns Err(String) if either the exponent or significand is out of range.
    pub fn from_data(is_negative: bool,
                     exponent: i32,
                     significand: u32)
                     -> Result<Decimal32, String> {
        if exponent < -101 {
            Err("Exponent cannot be less than -101.".to_string())
        } else if exponent > 90 {
            Err("Exponent cannot be greater than 90.".to_string())
        } else if significand > 9_999_999 {
            Err("Significand cannot be greater than 9,999,999.".to_string())
        } else {
            let sign_field = (if is_negative { 1 } else { 0 }) << 31;
            let stored_exponent = (exponent + 101) as u32;

            let implicit_field;
            let exponent_field;
            let significand_field;
            if significand < 8_388_608 {
                implicit_field = 0;
                exponent_field = stored_exponent << 23; // TODO think
                significand_field = significand;
            } else {
                // 8,388,608 is the first number that requires the implicit (100) in the significand
                implicit_field = 0b11 << 29;
                exponent_field = stored_exponent << 21;
                // remove the implicit (100)
                significand_field = significand - 0b1000_0000_0000_0000_0000_0000;
            }
            let ok_result = Decimal32 {
                data: sign_field + implicit_field + exponent_field + significand_field
            };
            Ok(ok_result)
        }
    }

    /// Creates and initializes a Decimal32 representation of positive infinity.
    pub fn infinity() -> Decimal32 {
        Decimal32 { data: 0b0_11110_000000_00000000000000000000 }
    }

    /// Creates and initializes a Decimal32 representation of negative infinity.
    pub fn neg_infinity() -> Decimal32 {
        Decimal32 { data: 0b1_11110_000000_00000000000000000000 }
    }

    /// Creates and initializes a Decimal32 that is specially encoded as a quiet NaN.
    pub fn quiet_nan() -> Decimal32 {
        Decimal32 { data: 0b0_11111_000000_00000000000000000000 }
    }

    /// Creates and initializes a Decimal32 that is specially encoded as a quiet NaN.
    pub fn qnan() -> Decimal32 {
        Decimal32 { data: 0b0_11111_000000_00000000000000000000 }
    }

    /// Creates and initializes a Decimal32 that is specially encoded as a signaling NaN.
    pub fn signaling_nan() -> Decimal32 {
        Decimal32 { data: 0b0_11111_100000_00000000000000000000 }
    }

    /// Creates and initializes a Decimal32 that is specially encoded as a signaling NaN.
    pub fn snan() -> Decimal32 {
        Decimal32 { data: 0b0_11111_100000_00000000000000000000 }
    }

    /// Returns a Decimal32 with the exact bits passed in through `data`.
    pub fn from_bin(data: u32) -> Decimal32 {
        Decimal32 { data: data }
    }

    pub fn to_f64(&self) -> f64 {
        let (is_negative, exponent, significand) = self.get_data();
        let multiplier = if is_negative { -1.0 } else { 1.0 };
        multiplier * 10f64.powi(exponent) * (significand as f64)
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

    /// Returns the three defining pieces of the decimal - the sign (true if negative), the
    /// exponent, and the significand, respectively.
    ///
    /// Do not expect well-behaved results if this decimal is NaN or infinity.
    pub fn get_data(&self) -> (bool, i32, u32) {
        // While it would be nice to make this method simply return (self.get_sign(),
        // self.get_exponent(), and self.get_significand()), that would require two duplicate checks
        // on the combination field.
        let sign = self.get_sign_field() != 0;
        let (exponent, significand) = if self.get_first_two_bits_combination_field() < 3 {
            ((self.get_normal_exponent() as i32) - 101, self.get_normal_significand())
        } else { // self.get_second_two_bits_combination_field() < 3
            ((self.get_shifted_exponent() as i32) - 101, self.get_shifted_significand())
        };
        (sign, exponent, significand)
    }

    /// Returns this Decimal32's exponent value.
    ///
    /// Do not expect well-behaved results if this decimal is NaN or infinity.
    pub fn get_exponent(&self) -> i32 {
        let exponent = if self.get_first_two_bits_combination_field() < 3 {
            self.get_normal_exponent()
        } else { // self.get_second_two_bits_combination_field() < 3
            self.get_shifted_exponent()
        };
        (exponent as i32) - 101
    }

    /// Returns this Decimal32's significand value.
    ///
    /// Do not expect well-behaved results if this decimal is NaN or infinity.
    pub fn get_significand(&self) -> u32 {
        if self.get_first_two_bits_combination_field() < 3 {
            self.get_normal_significand()
        } else { // self.get_second_two_bits_combination_field() < 3
            self.get_shifted_significand()
        }
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
        let mask: u32 = 0b0_11111_111000_00000000000000000000;
        (self.data & mask) >> 23
    }

    fn get_shifted_exponent(&self) -> u32 {
        let mask: u32 = 0b0_00111_111110_00000000000000000000;
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

    fn shift_exponent(&self, factor: i32) -> Result<Decimal32, String> {
        let (sign, exponent, significand) = self.get_data();
        let shifted_exponent = exponent + factor;
        let shifted_significand = ((significand as f64) * 10f64.powi(-factor)) as u32;
        Decimal32::from_data(sign, shifted_exponent, shifted_significand)
    }
}

impl Default for Decimal32 {
    fn default() -> Decimal32 {
        Decimal32::zero()
    }
}

// let width = match formatter.width() {
//     Some(width) => width,
//     None => 0
// };
// let precision = match formatter.precision() {
//     Some(precision) => precision,
//     None => 0
// };
impl fmt::Display for Decimal32 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        use super::super::zero_pad::{pad_right, pad_left};

        let (is_negative, exponent, significand) = self.get_data();

        let digits = significand.to_string();
        let num_significant_digits = digits.len() as i32;

        let sign = if is_negative { "-".to_string() } else { "".to_string() };

        let pos_decimal_str = if exponent >= 0 {
            pad_right(&digits, exponent as usize)
        } else if exponent > -num_significant_digits {
            let num_left_digits = (num_significant_digits + exponent) as usize;
            let left = digits[0..num_left_digits].to_string();
            let right = digits[num_left_digits..].to_string();
            left + "." + &right
        } else {
            let right = pad_left(&digits, ((-exponent) - num_significant_digits) as usize);
            "0.".to_string() + &right
        };

        let decimal_str = sign + &pos_decimal_str;
        write!(formatter, "{}", decimal_str)
    }
}

impl fmt::LowerExp for Decimal32 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}

impl fmt::UpperExp for Decimal32 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}

impl Add<Decimal32> for Decimal32 {
    type Output = Decimal32;

    fn add(self, other: Decimal32) -> Decimal32 {
        let sign = self.get_sign_field();

        if self.is_nan() || other.is_nan() {
            // if either operand is NaN, so is the result
            Decimal32::qnan()
        } else if self.is_infinity() {
            if self.is_positive() {
                if other.is_neg_infinity() {
                    // if the operands are opposing infinities, the result is sNaN
                    Decimal32::snan()
                } else {
                    // if the left operand is positive infinity, and the other is not negative
                    // infinity or NaN, the result is positive infinity
                    Decimal32::infinity()
                }
            } else {
                if other.is_pos_infinity() {
                    // if the operands are opposing infinities, the result is sNaN
                    Decimal32::snan()
                } else {
                    // if the left operand is negative infinity, and the other is not positive
                    // infinity or NaN, the result is negative infinity
                    Decimal32::neg_infinity()
                }
            }
        } else if other.is_infinity() {
            if other.is_positive() {
                if self.is_neg_infinity() {
                    // if the operands are opposing infinities, the result is sNaN
                    Decimal32::snan()
                } else {
                    // if the left operand is positive infinity, and the other is not negative
                    // infinity or NaN, the result is positive infinity
                    Decimal32::infinity()
                }
            } else {
                if self.is_pos_infinity() {
                    // if the operands are opposing infinities, the result is sNaN
                    Decimal32::snan()
                } else {
                    // if the left operand is negative infinity, and the other is not positive
                    // infinity or NaN, the result is negative infinity
                    Decimal32::neg_infinity()
                }
            }
        } else {
            let exponent;
            let significand;
            if self.get_first_two_bits_combination_field() < 3 {
                exponent = self.get_normal_exponent();
                significand = self.get_normal_significand();
            } else {
                // self.get_second_two_bits_combination_field() < 3
                exponent = self.get_shifted_exponent();
                significand = self.get_shifted_significand();
            }
            unimplemented!() // TODO
        }
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
    /// Returns the absolute value of this decimal, by returning a copy of this decimal with the
    /// sign bit turned off.
    fn abs(&self) -> Decimal32 {
        Decimal32 { data: self.data & (!SIGN_MASK) }
    }

    fn abs_sub(&self, other: &Decimal32) -> Decimal32 {
        // TODO
        // The positive difference of two numbers.
        // Returns zero if the number is less than or equal to other, otherwise the difference between self and other is returned.
        *self
    }

    /// Returns the sign of this decimal as a decimal.
    ///
    /// - 1.0 if the decimal is positive, +0.0 or INFINITY.
    /// - -1.0 if the decimal is negative, -0.0 or -INFINITY.
    /// - NaN if the decimal is NaN.
    fn signum(&self) -> Decimal32 {
        if self.is_nan() {
            self.clone()
        } else if self.is_positive() {
            Decimal32::one()
        } else {
            -Decimal32::one()
        }
    }

    /// Returns true if this decimal is positive, false otherwise.
    ///
    /// Note: Both zero and NaN can be positive or negative.
    fn is_positive(&self) -> bool {
        self.get_sign_field() == 0
    }

    /// Returns true if this decimal is negative, false otherwise.
    /// Note: Both zero and NaN can be positive or negative.
    fn is_negative(&self) -> bool {
        self.get_sign_field() != 0
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn get_exponent() {
        let zero = Decimal32 {
            // 101 => 0b0110_0101
            data: 0b0_01100101_00000000000000000000000
        };
        let expected = 0;
        let actual = zero.get_exponent();
        assert_eq!(expected, actual);

        let one = Decimal32 {
            // 102 => 0b0110_0110
            data: 0b0_01100110_00000000000000000000000
        };
        let expected = 1;
        let actual = one.get_exponent();
        assert_eq!(expected, actual);

        let neg_one = Decimal32 {
            // 100 => 0b0110_0101
            data: 0b0_01100100_00000000000000000000000
        };
        let expected = -1;
        let actual = neg_one.get_exponent();
        assert_eq!(expected, actual);

        let ninety = Decimal32 {
            // 100 => 0b0110_0101
            data: 0b0_10111111_00000000000000000000000
        };
        let expected = 90;
        let actual = ninety.get_exponent();
        assert_eq!(expected, actual);

        let neg_101 = Decimal32 {
            // 0 => 0b0000_0000
            data: 0b0_00000000_00000000000000000000000
        };
        let expected = -101;
        let actual = neg_101.get_exponent();
        assert_eq!(expected, actual);

        let alternate = Decimal32 {
            // 64 => 0b0100_0000
            data: 0b0_11_01000000_000000000000000000000
        };
        let expected = -37;
        let actual = alternate.get_exponent();
        assert_eq!(expected, actual);
    }

    #[test]
    fn get_significand() {
        let zero = Decimal32 {
            data: 0b0_0000000_00000000000000000000000
        };
        let expected = 0;
        let actual = zero.get_significand();
        assert_eq!(expected, actual);

        let one = Decimal32 {
            data: 0b0_0000000_00000000000000000000001
        };
        let expected = 1;
        let actual = one.get_significand();
        assert_eq!(expected, actual);

        let eighty = Decimal32 {
            // 80 => 0b0101_0000
            data: 0b0_00000000_00000000000000001010000
        };
        let expected = 80;
        let actual = eighty.get_significand();
        assert_eq!(expected, actual);

        let first_24th_bit = Decimal32 {
            data: 0b0_11_00000000_000000000000000000000
        };
        let expected = 8388608;
        let actual = first_24th_bit.get_significand();
        assert_eq!(expected, actual);

        let max = Decimal32 {
            data: 0b0_11_00000000_110001001011001111111
        };
        let expected = 9_999_999;
        let actual = max.get_significand();
        assert_eq!(expected, actual);
    }

    #[test]
    fn fmt() {
        let no_change = Decimal32::from_data(false, 0, 1234567).unwrap();
        let expected = "1234567".to_string();
        let actual = format!("{}", no_change);
        assert_eq!(expected, actual);

        let shift_left_one = Decimal32::from_data(false, 1, 1234567).unwrap();
        let expected = "12345670".to_string();
        let actual = format!("{}", shift_left_one);
        assert_eq!(expected, actual);

        let neg_shift_left_one = Decimal32::from_data(true, 1, 1234567).unwrap();
        let expected = "-12345670".to_string();
        let actual = format!("{}", neg_shift_left_one);
        assert_eq!(expected, actual);

        let shift_right_one = Decimal32::from_data(false, -1, 1234567).unwrap();
        let expected = "123456.7".to_string();
        let actual = format!("{}", shift_right_one);
        assert_eq!(expected, actual);

        let shift_right_four = Decimal32::from_data(false, -4, 12345).unwrap();
        let expected = "1.2345".to_string();
        let actual = format!("{}", shift_right_four);
        assert_eq!(expected, actual);

        let shift_right_seven = Decimal32::from_data(false, -7, 1234567).unwrap();
        let expected = "0.1234567".to_string();
        let actual = format!("{}", shift_right_seven);
        assert_eq!(expected, actual);

        let shift_right_ten = Decimal32::from_data(false, -10, 1234).unwrap();
        let expected = "0.0000001234".to_string();
        let actual = format!("{}", shift_right_ten);
        assert_eq!(expected, actual);
    }
}
