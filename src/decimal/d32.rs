use std::ops;
use std::fmt;

use num;
use num::{Num, Zero, One, Signed};

use super::parse_decimal_error::ParseDecimalError;

const NUM_DIGITS: u32 = 7;

const MIN_EXPONENT: i32 = -101;
const MAX_EXPONENT: i32 = 90;

const MIN_SIGNIFICAND: u32 = 0;
const MAX_SIGNIFICAND: u32 = 9999999;

const SIGN_MASK: u32 = 0b1_00000_000000_00000000000000000000;
const COMBINATION_MASK: u32 = 0b0_11111_000000_00000000000000000000;

/// Represents a 32-bit decimal number according to the [IEEE 754-2008 standard]
/// (https://en.wikipedia.org/wiki/Decimal32_floating-point_format).
///
/// Decimal32 supports 7 decimal digits of significand and an exponent range of −95 to +96, i.e.
/// ±0.000000×10^−95 to ±9.999999×10^96. (Equivalently, ±0000000×10^−101 to ±9999999×10^90.)
#[derive(Clone, Copy)]
pub struct d32 {
    bits: u32,
}

pub mod consts {
    use super::d32;

    pub const ZERO: d32 = d32 { bits: 0b0_01100101_00000000000000000000000 };
    pub const ONE: d32 = d32 { bits: 0b0_01100101_00000000000000000000001 };

    pub const MAX_VALUE: d32 = d32 { bits: 0b0_11_10111111_110001001011001111111 };
    pub const MIN_VALUE: d32 = d32 { bits: 0b1_11_10111111_110001001011001111111 };

    pub const INFINITY: d32 = d32 { bits: 0b0_11110_000000_00000000000000000000 };
    pub const NEG_INFINITY: d32 = d32 { bits: 0b1_11110_000000_00000000000000000000 };
    pub const QNAN: d32 = d32 { bits: 0b0_11111_000000_00000000000000000000 };
    pub const SNAN: d32 = d32 { bits: 0b0_11111_100000_00000000000000000000 };
    pub const NAN: d32 = QNAN;
}

impl d32 {
    /// Creates and initializes a d32 representation of zero.
    pub fn new() -> d32 {
        d32::zero()
    }

    /// Creates and initialize a decimal32 from its significant parts: the sign, exponent, and
    /// significand, respectively.
    ///
    /// If the exponent is out of range (less than -101 or greater than 90), the data will be
    /// shifted in an attempt to be fit into the 32-bit representation. If the shifted components
    /// still do not fit, the result may end in an "unexpected" value (i.e. ±infinity or zero)
    pub fn from_data(is_negative: bool, exponent: i32, significand: u32) -> d32 {
        if exponent < MIN_EXPONENT {
            let shift = MIN_EXPONENT - exponent;
            let (shifted_exponent, shifted_significand) =
                shift_exponent(significand, exponent, shift);
            // Retry with shifted exponent
            d32::from_data(is_negative, shifted_exponent, shifted_significand)
        } else if exponent > MAX_EXPONENT {
            let shift = MAX_EXPONENT - exponent;
            let (shifted_exponent, shifted_significand) =
                shift_exponent(significand, exponent, shift);
            // Retry with shifted exponent
            d32::from_data(is_negative, shifted_exponent, shifted_significand)
        } else if significand > MAX_SIGNIFICAND {
            if is_negative {
                consts::NEG_INFINITY
            } else {
                consts::INFINITY
            }
        } else {
            let sign_field = (if is_negative { 1 } else { 0 }) << 31;
            let biased_exponent = (exponent - MIN_EXPONENT) as u32;

            let implicit_field;
            let exponent_field;
            let significand_field;
            if significand < 8_388_608 {
                implicit_field = 0;
                exponent_field = biased_exponent << 23; // TODO think
                significand_field = significand;
            } else {
                // 8,388,608 is the first number that requires the implicit (100) in the significand
                implicit_field = 0b11 << 29;
                exponent_field = biased_exponent << 21;
                // remove the implicit (100)
                significand_field = significand - 0b1000_0000_0000_0000_0000_0000;
            }
            d32 { bits: sign_field + implicit_field + exponent_field + significand_field }
        }
    }

    /// Returns a d32 with the exact bits passed in through `data`.
    pub fn from_bin(data: u32) -> d32 {
        d32 { bits: data }
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
            ((self.get_normal_exponent() as i32) + MIN_EXPONENT, self.get_normal_significand())
        } else {
            // self.get_second_two_bits_combination_field() < 3
            ((self.get_shifted_exponent() as i32) + MIN_EXPONENT, self.get_shifted_significand())
        };
        (sign, exponent, significand)
    }

    /// Returns this d32's exponent value.
    ///
    /// Do not expect well-behaved results if this decimal is NaN or infinity.
    pub fn get_exponent(&self) -> i32 {
        let exponent = if self.get_first_two_bits_combination_field() < 3 {
            self.get_normal_exponent()
        } else {
            // self.get_second_two_bits_combination_field() < 3
            self.get_shifted_exponent()
        };
        (exponent as i32) + MIN_EXPONENT
    }

    /// Returns this d32's significand value.
    ///
    /// Do not expect well-behaved results if this decimal is NaN or infinity.
    pub fn get_significand(&self) -> u32 {
        if self.get_first_two_bits_combination_field() < 3 {
            self.get_normal_significand()
        } else {
            // self.get_second_two_bits_combination_field() < 3
            self.get_shifted_significand()
        }
    }

    fn get_sign_field(&self) -> u32 {
        (self.bits & SIGN_MASK) >> 31
    }

    fn get_combination_field(&self) -> u32 {
        (self.bits & COMBINATION_MASK) >> 26
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
        (self.bits & mask) >> 23
    }

    fn get_shifted_exponent(&self) -> u32 {
        let mask: u32 = 0b0_00111_111110_00000000000000000000;
        (self.bits & mask) >> 21
    }

    fn get_normal_significand(&self) -> u32 {
        let mask = 0b0_00000_000111_11111111111111111111;
        self.bits & mask
    }

    fn get_shifted_significand(&self) -> u32 {
        let implicit_100 = 0b100_0_00000_00000_00000_00000;
        let mask = 0b0_00000_000001_11111111111111111111;
        implicit_100 + (self.bits & mask)
    }
}

fn shift_exponent(significand: u32, exponent: i32, shift: i32) -> (i32, u32) {
    let shifted_exponent = exponent + shift;
    let pow_shift = num::pow(10u32, num::abs(shift) as usize);
    let shifted_significand = if shift < 0 {
        significand * pow_shift
    } else {
        significand / pow_shift
    };
    (shifted_exponent, shifted_significand)
}

fn to_common_exponent(left: &d32, right: &d32) -> (bool, u32, bool, u32, i32) {
    use std::cmp::Ordering;

    let (left_neg, left_exponent, left_significand) = left.get_data();
    let (right_neg, right_exponent, right_significand) = right.get_data();
    match left_exponent.cmp(&right_exponent) {
        Ordering::Equal => {
            (left_neg, left_significand, right_neg, right_significand, left_exponent)
        }
        Ordering::Less => {
            let shift = num::pow(10u32, (right_exponent - left_exponent) as usize);
            (left_neg, left_significand, right_neg, right_significand * shift, left_exponent)
        }
        Ordering::Greater => {
            let shift = num::pow(10u32, (left_exponent - right_exponent) as usize);
            (left_neg, left_significand * shift, right_neg, right_significand, right_exponent)
        }
    }
}

impl Default for d32 {
    fn default() -> d32 {
        d32::zero()
    }
}

impl PartialEq for d32 {
    fn eq(&self, other: &d32) -> bool {
        if self.is_zero() && other.is_zero() {
            return true;
        }
        if self.get_sign_field() != other.get_sign_field() {
            return false;
        }
        if self.is_infinity() && other.is_infinity() {
            assert_eq!(self.get_sign_field(), other.get_sign_field());
            return true;
        }
        if self.is_nan() && other.is_nan() {
            return false;
        }
        let (left_is_neg, left_significand, right_is_neg, right_significand, _) =
            to_common_exponent(&self, &other);
        left_is_neg == right_is_neg && left_significand == right_significand
    }
}

impl ops::Neg for d32 {
    type Output = d32;

    fn neg(self) -> d32 {
        d32 { bits: self.bits ^ 1 << 31 }
    }
}

impl ops::Add<d32> for d32 {
    type Output = d32;

    fn add(self, other: d32) -> d32 {
        if self.is_nan() || other.is_nan() {
            // if either operand is NaN, so is the result
            consts::NAN
        } else if self.is_infinity() {
            if self.is_positive() {
                if other.is_neg_infinity() {
                    // if the operands are opposing infinities, the result is NaN
                    consts::NAN
                } else {
                    // if the left operand is positive infinity, and the other is not negative
                    // infinity or NaN, the result is positive infinity
                    consts::INFINITY
                }
            } else {
                if other.is_pos_infinity() {
                    // if the operands are opposing infinities, the result is NaN
                    consts::NAN
                } else {
                    // if the left operand is negative infinity, and the other is not positive
                    // infinity or NaN, the result is negative infinity
                    consts::NEG_INFINITY
                }
            }
        } else if other.is_infinity() {
            if other.is_positive() {
                if self.is_neg_infinity() {
                    // if the operands are opposing infinities, the result is NaN
                    consts::NAN
                } else {
                    // if the left operand is positive infinity, and the other is not negative
                    // infinity or NaN, the result is positive infinity
                    consts::INFINITY
                }
            } else {
                if self.is_pos_infinity() {
                    // if the operands are opposing infinities, the result is NaN
                    consts::NAN
                } else {
                    // if the left operand is negative infinity, and the other is not positive
                    // infinity or NaN, the result is negative infinity
                    consts::NEG_INFINITY
                }
            }
        } else {
            let (left_is_neg, left_significand, right_is_neg, right_significand, exponent) =
                to_common_exponent(&self, &other);

            let signed_left_significand = if left_is_neg {
                -(left_significand as i32)
            } else {
                (left_significand as i32)
            };
            let signed_right_significand = if right_is_neg {
                -(right_significand as i32)
            } else {
                (right_significand as i32)
            };

            let signed_sum_significand: i32 = signed_left_significand + signed_right_significand;
            let sum_is_negative = signed_sum_significand < 0;
            let unsigned_sum_significand = num::abs(signed_sum_significand) as u32;
            d32::from_data(sum_is_negative, exponent, unsigned_sum_significand)
        }
    }
}

impl ops::Sub<d32> for d32 {
    type Output = d32;

    fn sub(self, other: d32) -> d32 {
        self // TODO
    }
}

impl ops::Mul<d32> for d32 {
    type Output = d32;

    fn mul(self, other: d32) -> d32 {
        self // TODO
    }
}

impl ops::Div<d32> for d32 {
    type Output = d32;

    fn div(self, other: d32) -> d32 {
        self // TODO
    }
}

impl ops::Rem<d32> for d32 {
    type Output = d32;

    fn rem(self, other: d32) -> d32 {
        self // TODO
    }
}

impl Num for d32 {
    type FromStrRadixErr = ParseDecimalError;

    fn from_str_radix(s: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        Ok(d32::zero()) // TODO
    }
}

impl Zero for d32 {
    fn zero() -> d32 {
        consts::ZERO
    }

    fn is_zero(&self) -> bool {
        (!self.is_infinity() && !self.is_nan()) && self.get_significand() == 0
    }
}

impl One for d32 {
    fn one() -> d32 {
        consts::ONE
    }
}

impl Signed for d32 {
    /// Returns the absolute value of this decimal, by returning a copy of this decimal with the
    /// sign bit turned off.
    fn abs(&self) -> d32 {
        d32 { bits: self.bits & (!SIGN_MASK) }
    }

    fn abs_sub(&self, other: &d32) -> d32 {
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
    fn signum(&self) -> d32 {
        if self.is_nan() {
            self.clone()
        } else if self.is_positive() {
            d32::one()
        } else {
            -d32::one()
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

impl fmt::Debug for d32 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let debug_str = if self.is_infinity() {
            if self.is_positive() {
                "d32::consts::INFINITY".to_string()
            } else {
                "d32::consts::NEG_INFINITY".to_string()
            }
        } else if self.is_nan() {
            "d32::consts::NAN".to_string()
        } else {
            let (is_negative, exponent, significand) = self.get_data();
            format!("d32 {{ is_negative: {}, exponent: {}, significand: {} }}",
                    is_negative,
                    exponent,
                    significand)
        };

        write!(formatter, "{}", debug_str)
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
impl fmt::Display for d32 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        use super::super::zero_pad::{pad_right, pad_left};

        let (is_negative, exponent, significand) = self.get_data();

        let digits = significand.to_string();
        let num_significant_digits = digits.len() as i32;

        let sign = if is_negative {
            "-".to_string()
        } else {
            "".to_string()
        };

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

impl fmt::LowerExp for d32 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!() // TODO
    }
}

impl fmt::UpperExp for d32 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!() // TODO
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn eq() {
        let zero1 = d32::from_data(true, 0, 0);
        let zero2 = d32::from_data(false, 11, 0);
        let zero3 = d32::from_data(true, 90, 0);
        let zero4 = d32::from_data(false, -101, 0);
        assert_eq!(zero1, zero2);
        assert_eq!(zero2, zero3);
        assert_eq!(zero3, zero4);
        assert_eq!(zero4, zero1);

        let one1 = d32::from_data(false, 0, 1);
        let one2 = d32::from_data(false, -1, 10);
        let one3 = d32::from_data(false, -2, 100);
        let one4 = d32::from_data(false, -3, 1000);
        assert_eq!(one1, one2);
        assert_eq!(one2, one3);
        assert_eq!(one3, one4);
        assert_eq!(one4, one1);

        let hundred1 = d32::from_data(false, 1, 100);
        let hundred2 = d32::from_data(false, 2, 10);
        let hundred3 = d32::from_data(false, 3, 1);
        assert_eq!(hundred1, hundred2);
        assert_eq!(hundred2, hundred3);
        assert_eq!(hundred3, hundred1);
    }

    #[test]
    fn from_data_overflow() {
        let expected = d32::from_data(false, 90, 10);
        let actual = d32::from_data(false, 91, 1);
        assert_eq!(expected, actual);

        let expected = d32::from_data(false, 90, 1090000);
        let actual = d32::from_data(false, 94, 109);
        assert_eq!(expected, actual);

        let expected = d32::from_data(false, -101, 1);
        let actual = d32::from_data(false, -102, 10);
        assert_eq!(expected, actual);

        let expected = d32::from_data(true, -101, 1);
        let actual = d32::from_data(true, -102, 10);
        assert_eq!(expected, actual);

        let expected = d32::from_data(false, -101, 0);
        let actual = d32::from_data(false, -102, 1);
        assert_eq!(expected, actual);

        let expected = consts::INFINITY;
        let actual = d32::from_data(false, 94, 9999999);
        assert_eq!(expected, actual);

        let expected = consts::NEG_INFINITY;
        let actual = d32::from_data(true, 94, 9999999);
        assert_eq!(expected, actual);
    }

    #[test]
    fn get_exponent() {
        let zero = d32 {
            // 101 => 0b0110_0101
            bits: 0b0_01100101_00000000000000000000000,
        };
        let expected = 0;
        let actual = zero.get_exponent();
        assert_eq!(expected, actual);

        let one = d32 {
            // 102 => 0b0110_0110
            bits: 0b0_01100110_00000000000000000000000,
        };
        let expected = 1;
        let actual = one.get_exponent();
        assert_eq!(expected, actual);

        let neg_one = d32 {
            // 100 => 0b0110_0101
            bits: 0b0_01100100_00000000000000000000000,
        };
        let expected = -1;
        let actual = neg_one.get_exponent();
        assert_eq!(expected, actual);

        let ninety = d32 {
            // 100 => 0b0110_0101
            bits: 0b0_10111111_00000000000000000000000,
        };
        let expected = 90;
        let actual = ninety.get_exponent();
        assert_eq!(expected, actual);

        let neg_101 = d32 {
            // 0 => 0b0000_0000
            bits: 0b0_00000000_00000000000000000000000,
        };
        let expected = -101;
        let actual = neg_101.get_exponent();
        assert_eq!(expected, actual);

        let alternate = d32 {
            // 64 => 0b0100_0000
            bits: 0b0_11_01000000_000000000000000000000,
        };
        let expected = -37;
        let actual = alternate.get_exponent();
        assert_eq!(expected, actual);
    }

    #[test]
    fn get_significand() {
        let zero = d32 { bits: 0b0_0000000_00000000000000000000000 };
        let expected = 0;
        let actual = zero.get_significand();
        assert_eq!(expected, actual);

        let one = d32 { bits: 0b0_0000000_00000000000000000000001 };
        let expected = 1;
        let actual = one.get_significand();
        assert_eq!(expected, actual);

        let eighty = d32 {
            // 80 => 0b0101_0000
            bits: 0b0_00000000_00000000000000001010000,
        };
        let expected = 80;
        let actual = eighty.get_significand();
        assert_eq!(expected, actual);

        let first_24th_bit = d32 { bits: 0b0_11_00000000_000000000000000000000 };
        let expected = 8388608;
        let actual = first_24th_bit.get_significand();
        assert_eq!(expected, actual);

        let max = d32 { bits: 0b0_11_00000000_110001001011001111111 };
        let expected = 9_999_999;
        let actual = max.get_significand();
        assert_eq!(expected, actual);
    }

    #[test]
    fn fmt() {
        let no_change = d32::from_data(false, 0, 1234567);
        let expected = "1234567".to_string();
        let actual = format!("{}", no_change);
        assert_eq!(expected, actual);

        let shift_left_one = d32::from_data(false, 1, 1234567);
        let expected = "12345670".to_string();
        let actual = format!("{}", shift_left_one);
        assert_eq!(expected, actual);

        let neg_shift_left_one = d32::from_data(true, 1, 1234567);
        let expected = "-12345670".to_string();
        let actual = format!("{}", neg_shift_left_one);
        assert_eq!(expected, actual);

        let shift_right_one = d32::from_data(false, -1, 1234567);
        let expected = "123456.7".to_string();
        let actual = format!("{}", shift_right_one);
        assert_eq!(expected, actual);

        let shift_right_four = d32::from_data(false, -4, 12345);
        let expected = "1.2345".to_string();
        let actual = format!("{}", shift_right_four);
        assert_eq!(expected, actual);

        let shift_right_seven = d32::from_data(false, -7, 1234567);
        let expected = "0.1234567".to_string();
        let actual = format!("{}", shift_right_seven);
        assert_eq!(expected, actual);

        let shift_right_ten = d32::from_data(false, -10, 1234);
        let expected = "0.0000001234".to_string();
        let actual = format!("{}", shift_right_ten);
        assert_eq!(expected, actual);
    }

    #[test]
    fn add() {
        let zero = consts::ZERO;
        let one = ONE;
        let pos_infinity = consts::INFINITY;
        let neg_infinity = consts::NEG_INFINITY;
        let nan = consts::NAN;

        assert_eq!(one, zero + one);

        let two1 = d32::from_data(false, -1, 20);
        assert_eq!(two1, one + one);

        let two2 = d32::from_data(false, -2, 200);
        assert_eq!(two2, one + one);

        let eighteen = d32::from_data(false, -2, 1800);
        let mut sum = consts::ZERO;
        for _ in 0..18 {
            sum = sum + one;
        }
        assert_eq!(eighteen, sum);

        assert!((MAX_VALUE + MAX_VALUE).is_infinity());
        assert!((consts::MIN_VALUE + consts::MIN_VALUE).is_neg_infinity());

        // special values
        assert_eq!(pos_infinity, pos_infinity + pos_infinity);
        assert_eq!(neg_infinity, neg_infinity + neg_infinity);

        assert!((pos_infinity + neg_infinity).is_nan());
        assert!((neg_infinity + pos_infinity).is_nan());

        assert!((nan + zero).is_nan());
        assert!((nan + one).is_nan());
        assert!((nan + nan).is_nan());
    }
}
