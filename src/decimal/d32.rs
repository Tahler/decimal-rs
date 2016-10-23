use std::cmp;
use std::ops;
use std::fmt;

use num;
use num::{Num, Zero, One, Signed};

use bit_ops;

use super::parse_decimal_error::ParseDecimalError;

const NUM_DIGITS: u32 = 7;

const MIN_EXPONENT: i32 = -101;
const MAX_EXPONENT: i32 = 90;

const MIN_SIGNIFICAND: u32 = 0;
const MAX_SIGNIFICAND: u32 = 9999999;

/// Represents a 32-bit decimal number according to the [IEEE 754-2008 standard]
/// (https://en.wikipedia.org/wiki/Decimal32_floating-point_format).
///
/// Decimal32 supports 7 decimal digits of significand and an exponent range of −95 to +96, i.e.
/// ±0.000000×10^−95 to ±9.999999×10^96. (Equivalently, ±0000000×10^−101 to ±9999999×10^90.)
#[allow(non_camel_case_types)]
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
            let shifted_components = shift_exponent(significand, exponent, shift);
            match shifted_components {
                // Retry with shifted exponent
                Some((shifted_exponent, shifted_significand)) => d32::from_data(is_negative, shifted_exponent, shifted_significand),
                None => consts::ZERO,
            }
        } else if exponent > MAX_EXPONENT {
            let shift = MAX_EXPONENT - exponent;
            let shifted_components = shift_exponent(significand, exponent, shift);
            match shifted_components {
                // Retry with shifted exponent
                Some((shifted_exponent, shifted_significand)) => d32::from_data(is_negative, shifted_exponent, shifted_significand),
                None => if is_negative {
                    consts::NEG_INFINITY
                } else {
                    consts::INFINITY
                },
            }
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
        bit_ops::get_bits(self.bits, 31, 32)
    }

    fn get_combination_field(&self) -> u32 {
        bit_ops::get_bits(self.bits, 26, 30)
    }

    fn get_first_two_bits_combination_field(&self) -> u32 {
        let combination_field = self.get_combination_field();
        bit_ops::get_bits(combination_field, 3, 5)
    }

    fn get_second_two_bits_combination_field(&self) -> u32 {
        let combination_field = self.get_combination_field();
        bit_ops::get_bits(combination_field, 1, 3)
    }

    fn get_normal_exponent(&self) -> u32 {
        bit_ops::get_bits(self.bits, 23, 30)
    }

    fn get_shifted_exponent(&self) -> u32 {
        bit_ops::get_bits(self.bits, 21, 28)
    }

    fn get_normal_significand(&self) -> u32 {
        bit_ops::get_bits(self.bits, 0, 21)
    }

    fn get_shifted_significand(&self) -> u32 {
        let implicit_100 = 0b100_0_00000_00000_00000_00000;
        implicit_100 + bit_ops::get_bits(self.bits, 0, 20)
    }
}

fn shift_exponent(significand: u32, exponent: i32, shift: i32) -> Option<(i32, u32)> {
    let shifted_exponent = exponent + shift;
    let pow_shift = num::pow(10u32, num::abs(shift) as usize);
    // TODO: not happy about using Option here
    let shifted_significand = if shift < 0 {
        significand.checked_mul(pow_shift)
    } else {
        significand.checked_div(pow_shift)
    };
    match shifted_significand {
        Some(shifted_significand) => Some((shifted_exponent, shifted_significand)),
        None => None,
    }
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

impl cmp::PartialEq for d32 {
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

impl cmp::PartialOrd for d32 {
    fn partial_cmp(&self, other: &d32) -> Option<cmp::Ordering> {
        // NaN special case
        if self.is_nan() || other.is_nan() {
            // if either party is NaN, then the result is None (uncomparable)
            return None;
        }
        // Zero special cases (since zero's sign bit is irrelevant)
        if self.is_zero() {
            if other.is_zero() {
                return Some(cmp::Ordering::Equal);
            } else if other.is_positive() {
                return Some(cmp::Ordering::Less)
            } else {
                return Some(cmp::Ordering::Greater)
            }
        }
        if other.is_zero() {
            assert!(!self.is_zero());
            if self.is_positive() {
                return Some(cmp::Ordering::Greater)
            } else {
                return Some(cmp::Ordering::Less)
            }
        }
        // Normal case
        let lhs_sign_field = self.get_sign_field();
        let rhs_sign_field = other.get_sign_field();
        // panic!("{:?}, {:?}, {:?}", lhs_sign_field, rhs_sign_field, lhs_sign_field.partial_cmp(&rhs_sign_field));
        if lhs_sign_field != rhs_sign_field {
            // defer to the sign field comparison
            return rhs_sign_field.partial_cmp(&lhs_sign_field);
        }
        // Infinity special cases
        if self.is_infinity() && other.is_infinity() {
            assert!(lhs_sign_field == rhs_sign_field);
            return Some(cmp::Ordering::Equal)
        }
        let diff = (*self) - (*other);
        if diff.is_zero() {
            Some(cmp::Ordering::Equal)
        } else {
            if diff.is_positive() {
                Some(cmp::Ordering::Greater)
            } else {
                Some(cmp::Ordering::Less)
            }
        }
    }
}

impl ops::Neg for d32 {
    type Output = d32;

    fn neg(self) -> d32 {
        use super::super::bit_ops;

        // Flip the MSB (most significant bit)
        let msb_flipped = bit_ops::toggle_bit(self.bits, 31);

        d32 { bits: msb_flipped }
    }
}

impl ops::Add<d32> for d32 {
    type Output = d32;

    fn add(self, other: d32) -> d32 {
        if self.is_nan() || other.is_nan() {
            // NaN + anything = NaN
            consts::NAN
        } else if self.is_infinity() {
            if self.is_positive() {
                if other.is_neg_infinity() {
                    // Infinity + -Infinity = NaN
                    consts::NAN
                } else {
                    // Infinity + normal values = Infinity
                    consts::INFINITY
                }
            } else {
                if other.is_pos_infinity() {
                    // -Infinity + Infinity = NaN
                    consts::NAN
                } else {
                    // -Infinity + normal values = -Infinity
                    consts::NEG_INFINITY
                }
            }
        } else if other.is_infinity() {
            assert!(!self.is_infinity());
            if other.is_positive() {
                // normal values + Infinity = Infinity
                consts::INFINITY
            } else {
                // normal values + -Infinity = -Infinity
                consts::NEG_INFINITY
            }
        } else {
            // Normal case
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
        self + (-other)
    }
}

impl ops::Mul<d32> for d32 {
    type Output = d32;

    fn mul(self, other: d32) -> d32 {
        use num::Signed;

        if self.is_nan() || other.is_nan() {
            // NaN * anything = NaN
            consts::NAN
        } else if self.is_infinity() {
            if other.is_zero() {
                // Inf * 0 = NaN
                consts::NAN
            } else {
                if self.is_positive() {
                    if other.is_positive() {
                        // Inf * anything positive = Inf
                        consts::INFINITY
                    } else {
                        // Inf * anything negative = -Inf
                        consts::NEG_INFINITY
                    }
                } else {
                    if other.is_positive() {
                        // -Inf * anything positive = -Inf
                        consts::NEG_INFINITY
                    } else {
                        // -Inf * anything negative = Inf
                        consts::INFINITY
                    }
                }
            }
        } else if other.is_infinity() {
            if self.is_zero() {
                // 0 * Inf = NaN
                consts::NAN
            } else {
                if other.is_positive() {
                    if self.is_positive() {
                        // anything positive * Inf = Inf
                        consts::INFINITY
                    } else {
                        // anything negative * Inf = -Inf
                        consts::NEG_INFINITY
                    }
                } else {
                    if self.is_positive() {
                        // anything positive * -Inf = -Inf
                        consts::NEG_INFINITY
                    } else {
                        // anything negative * -Inf = Inf
                        consts::INFINITY
                    }
                }
            }
        } else if self.is_zero() || other.is_zero() {
            // 0 * normal values = 0
            consts::ZERO
        } else if self == consts::ONE {
            // 1 * a normal value = the normal value
            other
        } else if other == consts::ONE {
            // a normal value * 1 = the normal value
            self
        } else {
            // Normal case
            let significand = self.get_significand() * other.get_significand();
            let exponent = self.get_exponent() + other.get_exponent();
            let sign = self.get_sign_field() ^ other.get_sign_field();
            d32::from_data(sign != 0, exponent, significand)
        }
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

impl num::Signed for d32 {
    /// Returns the absolute value of this decimal, by returning a copy of this decimal with the
    /// sign bit turned off.
    fn abs(&self) -> d32 {
        let with_sign_bit_off = bit_ops::clear_bit(self.bits, 31);
        d32 { bits: with_sign_bit_off }
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
    /// Note: Zero and NaN are neither positive or negative.
    fn is_positive(&self) -> bool {
        !self.is_nan() && !self.is_zero() && self.get_sign_field() == 0
    }

    /// Returns true if this decimal is negative, false otherwise.
    ///
    /// Note: Zero and NaN are neither positive or negative.
    fn is_negative(&self) -> bool {
        !self.is_nan() && !self.is_zero() && self.get_sign_field() != 0
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
mod tests {
    use super::*;

    #[test]
    fn test_get_exponent() {
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
    fn test_get_significand() {
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
    fn test_eq() {
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

        let nan = consts::NAN;
        assert!(nan != nan);

        let pos_infinity = consts::INFINITY;
        assert_eq!(pos_infinity, pos_infinity);

        let neg_infinity = consts::NEG_INFINITY;
        assert_eq!(neg_infinity, neg_infinity);
    }

    #[test]
    fn test_from_data_overflow() {
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

        let expected = consts::ZERO;
        let actual = d32::from_data(false, -106, 1949);
        assert_eq!(expected, actual);

        let expected = consts::INFINITY;
        let actual = d32::from_data(false, 94, 9999999);
        assert_eq!(expected, actual);

        let expected = consts::NEG_INFINITY;
        let actual = d32::from_data(true, 94, 9999999);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_sign_check() {
        use num::Signed;

        let one_hundred = d32::from_data(false, 1, 100);
        assert!(one_hundred.is_positive());
        assert!(!one_hundred.is_negative());

        let neg_one_hundred = d32::from_data(true, 1, 100);
        assert!(neg_one_hundred.is_negative());
        assert!(!neg_one_hundred.is_positive());

        let zero1 = d32::from_data(true, 0, 0);
        let zero2 = d32::from_data(false, 11, 0);
        assert!(!zero1.is_positive());
        assert!(!zero1.is_negative());
        assert!(!zero2.is_positive());
        assert!(!zero2.is_negative());

        let nan = consts::NAN;
        assert!(!nan.is_positive());
        assert!(!nan.is_negative());

        let pos_infinity = consts::INFINITY;
        assert!(pos_infinity.is_positive());
        assert!(!pos_infinity.is_negative());
        assert!(pos_infinity.is_pos_infinity());
        assert!(!pos_infinity.is_neg_infinity());

        let neg_infinity = consts::NEG_INFINITY;
        assert!(neg_infinity.is_negative());
        assert!(!neg_infinity.is_positive());
        assert!(neg_infinity.is_neg_infinity());
        assert!(!neg_infinity.is_pos_infinity());
    }

    #[test]
    fn test_ord() {
        let zero1 = d32::from_data(true, 0, 0);
        let zero2 = d32::from_data(false, 11, 0);
        assert!(!(zero1 < zero2));
        assert!(!(zero1 > zero2));
        assert!(zero1 >= zero2);
        assert!(zero1 <= zero2);
        assert!(zero1 >= zero1);

        let one_hundred = d32::from_data(false, 1, 100);
        assert!(zero1 < one_hundred);
        assert!(zero1 <= one_hundred);

        let neg_one_hundred = d32::from_data(true, 1, 100);
        assert!(zero1 > neg_one_hundred);
        assert!(zero1 >= neg_one_hundred);
        assert!(one_hundred >= neg_one_hundred);
        assert!(one_hundred > neg_one_hundred);
        assert!(neg_one_hundred < one_hundred);
        assert!(neg_one_hundred <= one_hundred);

        let nan = consts::NAN;
        assert!(!(nan < nan));
        assert!(!(nan <= nan));
        assert!(!(nan > nan));
        assert!(!(nan >= nan));

        let pos_infinity = consts::INFINITY;
        assert!(pos_infinity >= pos_infinity);

        let neg_infinity = consts::NEG_INFINITY;
        assert!(neg_infinity < pos_infinity);
        assert!(neg_infinity <= pos_infinity);
    }

    #[test]
    fn test_abs() {
        use num::Signed;

        let zero = consts::ZERO;
        assert_eq!(zero, zero.abs());

        let pos_infinity = consts::INFINITY;
        let neg_infinity = consts::NEG_INFINITY;
        assert_eq!(pos_infinity, pos_infinity.abs());
        assert_eq!(pos_infinity, neg_infinity.abs());

        let one = consts::ONE;
        let neg_one = d32::from_data(true, 0, 1);
        assert_eq!(one, one.abs());
        assert_eq!(one, neg_one.abs());

        let one_thousand_point_four = d32::from_data(false, -1, 10004);
        let neg_one_thousand_point_four = d32::from_data(true, -1, 10004);
        assert_eq!(one_thousand_point_four, one_thousand_point_four.abs());
        assert_eq!(one_thousand_point_four, neg_one_thousand_point_four.abs());
    }

    #[test]
    fn test_neg() {
        let zero = consts::ZERO;
        assert_eq!(zero, -zero);

        let pos_infinity = consts::INFINITY;
        let neg_infinity = consts::NEG_INFINITY;
        assert_eq!(pos_infinity, -neg_infinity);
        assert_eq!(neg_infinity, -pos_infinity);

        let one = consts::ONE;
        let neg_one = d32::from_data(true, 0, 1);
        assert_eq!(neg_one, -one);

        let one_thousand_point_four = d32::from_data(false, -1, 10004);
        let neg_one_thousand_point_four = d32::from_data(true, -1, 10004);
        assert_eq!(neg_one_thousand_point_four, -one_thousand_point_four);
    }

    #[test]
    fn test_add() {
        // TODO: test adding +0 and -0 to infinity
        let zero = consts::ZERO;
        let one = consts::ONE;
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

        assert!((consts::MAX_VALUE + consts::MAX_VALUE).is_infinity());
        assert!((consts::MIN_VALUE + consts::MIN_VALUE).is_neg_infinity());

        // special values
        let pos_infinity = consts::INFINITY;
        let neg_infinity = consts::NEG_INFINITY;
        assert_eq!(pos_infinity, pos_infinity + pos_infinity);
        assert_eq!(neg_infinity, neg_infinity + neg_infinity);
        assert!((pos_infinity + neg_infinity).is_nan());
        assert!((neg_infinity + pos_infinity).is_nan());

        let nan = consts::NAN;
        assert!((nan + zero).is_nan());
        assert!((nan + one).is_nan());
        assert!((nan + nan).is_nan());
    }

    #[test]
    fn test_sub() {
        let zero = consts::ZERO;
        let one = consts::ONE;
        assert_eq!(one, one - zero);

        assert_eq!(zero, one - one);

        let eighteen = d32::from_data(false, -2, 1800);
        let mut acc = eighteen;
        for _ in 0..18 {
            acc = acc - one;
        }
        assert_eq!(zero, acc);

        assert_eq!(zero, consts::MAX_VALUE - consts::MAX_VALUE);
        assert_eq!(zero, consts::MIN_VALUE - consts::MIN_VALUE);

        let pos_infinity = consts::INFINITY;
        let neg_infinity = consts::NEG_INFINITY;
        assert_eq!(pos_infinity, pos_infinity - neg_infinity);
        assert_eq!(neg_infinity, neg_infinity - pos_infinity);
        assert!((pos_infinity - pos_infinity).is_nan());
        assert!((neg_infinity - neg_infinity).is_nan());

        let nan = consts::NAN;
        assert!((nan - zero).is_nan());
        assert!((nan - one).is_nan());
        assert!((nan - nan).is_nan());
    }

    #[test]
    fn test_mul() {
        let zero = consts::ZERO;
        assert_eq!(zero, zero * zero);

        let one = consts::ONE;
        assert_eq!(zero, one * zero);
        assert_eq!(one, one * one);

        let two = d32::from_data(false, 0, 2);
        let four = d32::from_data(false, 0, 4);
        assert_eq!(four, two * two);

        let eighteen = d32::from_data(false, -2, 1800);
        assert_eq!(eighteen, one * eighteen);
        assert_eq!(eighteen, eighteen * one);

        let neg_seventy_two = d32::from_data(true, 0, 72);
        assert_eq!(neg_seventy_two, -four * eighteen);

        let three_hundred_twenty_four = d32::from_data(false, 0, 324);
        assert_eq!(three_hundred_twenty_four, eighteen * eighteen);
        assert_eq!(three_hundred_twenty_four, one * eighteen * eighteen);
        assert_eq!(three_hundred_twenty_four, one * eighteen * one * eighteen * one);
        assert_eq!(zero, one * eighteen * eighteen * zero);

        let pos_infinity = consts::INFINITY;
        let neg_infinity = consts::NEG_INFINITY;
        assert_eq!(neg_infinity, pos_infinity * neg_infinity);
        assert_eq!(neg_infinity, neg_infinity * pos_infinity);
        assert_eq!(pos_infinity, neg_infinity * neg_infinity);
        assert_eq!(pos_infinity, pos_infinity * two);
        assert_eq!(neg_infinity, pos_infinity * -two);
        assert!((pos_infinity * zero).is_nan());
        assert!((zero * neg_infinity).is_nan());

        let nan = consts::NAN;
        assert!((nan * zero).is_nan());
        assert!((nan * one).is_nan());
        assert!((nan * -four).is_nan());
        assert!((nan * nan).is_nan());
    }

    #[test]
    fn test_fmt() {
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
}
