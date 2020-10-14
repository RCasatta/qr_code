// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//
// taken from https://github.com/WanzenBug/g2p version 0.4.0

//! # g2poly
//!
//! A small library to handle polynomials of degree < 64 over the finite field GF(2).
//!
//! The main motivation for this library is generating finite fields of the form GF(2^p).
//! Elements of GF(2^p) can be expressed as polynomials over GF(2) with degree < p. These
//! finite fields are used in cryptographic algorithms as well as error detecting / correcting
//! codes.
//!
//! # Example
//!
//! ```rust
//! use qr_code::decode::g2poly;
//!
//! let a = g2poly::G2Poly(0b10011);
//! assert_eq!(format!("{}", a), "G2Poly { x^4 + x + 1 }");
//! let b = g2poly::G2Poly(0b1);
//! assert_eq!(a + b, g2poly::G2Poly(0b10010));
//!
//! // Since products could overflow in u64, the product is defined as a u128
//! assert_eq!(a * a, g2poly::G2PolyProd(0b100000101));
//!
//! // This can be reduced using another polynomial
//! let s = a * a % g2poly::G2Poly(0b1000000);
//! assert_eq!(s, g2poly::G2Poly(0b101));
//! ```

use core::{cmp, fmt, ops};

/// Main type exported by this library
///
/// The polynomial is represented as the bits of the inner `u64`. The least significant bit
/// represents `c_0` in `c_n * x^n + c_(n-1) * x^(n-1) + ... + c_0 * x^0`, the next bit c_1 and so on.
///
/// ```rust
/// use qr_code::decode::g2poly::G2Poly;
/// assert_eq!(format!("{}", G2Poly(0b101)), "G2Poly { x^2 + 1 }");
/// ```
///
/// 3 main operations [`+`](#impl-Add<G2Poly>), [`-`](#impl-Sub<G2Poly>) and
/// [`*`](#impl-Mul<G2Poly>) are implemented, as well as [`%`](#impl-Rem<G2Poly>) for remainder
/// calculation. Note that multiplication generates a `G2PolyProd` so there is no risk of
/// overflow.
///
/// Division is left out as there is generally not needed for common use cases. This may change in a
/// later release.
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct G2Poly(pub u64);

/// The result of multiplying two `G2Poly`
///
/// This type is used to represent the result of multiplying two `G2Poly`s. Since this could
/// overflow when relying on just a `u64`, this type uses an internal `u128`. The only operation
/// implemented on this type is [`%`](#impl-Rem<G2Poly>) which reduces the result back to a
/// `G2Poly`.
///
/// ```rust
/// use qr_code::decode::g2poly::{G2Poly, G2PolyProd};
/// let a = G2Poly(0xff_00_00_00_00_00_00_00);
/// assert_eq!(a * a, G2PolyProd(0x55_55_00_00_00_00_00_00_00_00_00_00_00_00_00_00));
/// assert_eq!(a * a % G2Poly(0b100), G2Poly(0));
/// ```
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct G2PolyProd(pub u128);

impl G2PolyProd {
    /// Convert to G2Poly
    ///
    /// # Panics
    /// Panics, if the internal representation exceeds the maximum value for G2Poly.
    ///
    /// # Example
    /// ```rust
    /// use qr_code::decode::g2poly::G2Poly;
    ///
    /// let a = G2Poly(0x40_00_00_00_00_00_00_00) * G2Poly(2);
    /// assert_eq!(G2Poly(0x80_00_00_00_00_00_00_00), a.to_poly());
    ///
    /// // Next line would panics!
    /// // (G2Poly(0x40_00_00_00_00_00_00_00) * G2Poly(4)).to_poly();
    /// ```
    pub fn to_poly(self) -> G2Poly {
        self.try_to_poly()
            .expect("Tried to convert product bigger than G2Poly max")
    }

    /// Convert to G2Poly if possible
    ///
    /// In case the value would not fit into `G2Poly`, return `None`
    ///
    /// # Example
    /// ```rust
    /// use qr_code::decode::g2poly::G2Poly;
    /// assert_eq!((G2Poly(0x40_00_00_00_00_00_00_00) * G2Poly(2)).try_to_poly(), Some(G2Poly(0x80_00_00_00_00_00_00_00)));
    /// assert_eq!((G2Poly(0x40_00_00_00_00_00_00_00) * G2Poly(4)).try_to_poly(), None);
    /// ```
    pub fn try_to_poly(self) -> Option<G2Poly> {
        if self.0 <= u64::max_value() as u128 {
            Some(G2Poly(self.0 as u64))
        } else {
            None
        }
    }
}

impl fmt::Debug for G2Poly {
    fn fmt<'a>(&self, f: &mut fmt::Formatter<'a>) -> fmt::Result {
        write!(f, "G2Poly {{ {:b} }}", self.0)
    }
}

impl fmt::Debug for G2PolyProd {
    fn fmt<'a>(&self, f: &mut fmt::Formatter<'a>) -> fmt::Result {
        write!(f, "G2PolyProd {{ {:b} }}", self.0)
    }
}

impl fmt::Display for G2Poly {
    fn fmt<'a>(&self, f: &mut fmt::Formatter<'a>) -> fmt::Result {
        if self.0 == 0 {
            return write!(f, "G2Poly {{ 0 }}");
        }

        write!(f, "G2Poly {{ ")?;
        let start = 63 - self.0.leading_zeros();
        let mut check = 1 << start;
        let mut append = false;
        for p in (0..=start).rev() {
            if check & self.0 > 0 {
                if append {
                    write!(f, " + ")?;
                }

                if p == 0 {
                    write!(f, "1")?;
                } else if p == 1 {
                    write!(f, "x")?;
                } else {
                    write!(f, "x^{}", p)?;
                }
                append = true;
            }
            check >>= 1;
        }
        write!(f, " }}")
    }
}

impl ops::Mul for G2Poly {
    type Output = G2PolyProd;

    fn mul(self, rhs: G2Poly) -> G2PolyProd {
        let mut result = 0;

        let smaller = cmp::min(self.0, rhs.0);
        let mut bigger = cmp::max(self.0, rhs.0) as u128;

        let end = 64 - smaller.leading_zeros();
        let mut bitpos = 1;
        for _ in 0..end {
            if bitpos & smaller > 0 {
                result ^= bigger;
            }
            bigger <<= 1;
            bitpos <<= 1;
        }

        G2PolyProd(result)
    }
}

impl ops::Rem for G2Poly {
    type Output = G2Poly;

    fn rem(self, rhs: G2Poly) -> G2Poly {
        G2PolyProd(self.0 as u128) % rhs
    }
}

impl ops::Div for G2Poly {
    type Output = G2Poly;

    /// Calculate the polynomial quotient
    ///
    /// For `a / b` calculate the value `q` in `a = q * b + r` such that
    /// |r| < |b|.
    ///
    /// # Example
    /// ```rust
    /// use qr_code::decode::g2poly::G2Poly;
    /// let a = G2Poly(0b0100_0000_0101);
    /// let b = G2Poly(0b1010);
    ///
    /// assert_eq!(G2Poly(0b101_01010), a / b);
    /// ```
    fn div(self, rhs: G2Poly) -> G2Poly {
        let divisor = rhs.0;
        let divisor_degree_p1 = 64 - divisor.leading_zeros();
        assert!(divisor_degree_p1 > 0);

        let mut quotient = 0;
        let mut rem = self.0;
        let mut rem_degree_p1 = 64 - self.0.leading_zeros();

        while divisor_degree_p1 <= rem_degree_p1 {
            let shift_len = rem_degree_p1 - divisor_degree_p1;
            quotient |= 1 << shift_len;
            rem ^= divisor << shift_len;
            rem_degree_p1 = 64 - rem.leading_zeros();
        }
        G2Poly(quotient)
    }
}

impl ops::Add for G2Poly {
    type Output = G2Poly;

    fn add(self, rhs: G2Poly) -> G2Poly {
        G2Poly(self.0 ^ rhs.0)
    }
}

impl ops::Sub for G2Poly {
    type Output = G2Poly;

    fn sub(self, rhs: G2Poly) -> G2Poly {
        G2Poly(self.0 ^ rhs.0)
    }
}

impl ops::Rem<G2Poly> for G2PolyProd {
    type Output = G2Poly;

    /// Calculate the polynomial remainder of the product of polynomials
    ///
    /// When calculating a % b this computes the value of r in
    /// `a = q * b + r` such that |r| < |b|.
    ///
    /// # Example
    /// ```rust
    /// use qr_code::decode::g2poly::G2Poly;
    /// let a = G2Poly(0x12_34_56_78_9A_BC_DE);
    /// let m = G2Poly(0x00_00_00_01_00_00);
    /// assert!((a * a % m).degree().expect("Positive degree") < m.degree().expect("Positive degree"));
    /// assert_eq!(G2Poly(0b0101_0001_0101_0100), a * a % m);
    /// ```
    fn rem(self, rhs: G2Poly) -> G2Poly {
        let module = rhs.0 as u128;
        let mod_degree_p1 = 128 - module.leading_zeros();
        assert!(mod_degree_p1 > 0);

        let mut rem = self.0;
        let mut rem_degree_p1 = 128 - rem.leading_zeros();

        while mod_degree_p1 <= rem_degree_p1 {
            let shift_len = rem_degree_p1 - mod_degree_p1;
            rem ^= module << shift_len;
            rem_degree_p1 = 128 - rem.leading_zeros();
        }

        // NB: rem_degree < mod_degree implies that rem < mod so it fits in u64
        G2Poly(rem as u64)
    }
}

/// Calculate the greatest common divisor of `a` and `b`
///
/// This uses the classic euclidean algorithm to determine the greatest common divisor of two
/// polynomials.
///
/// # Example
/// ```rust
/// use qr_code::decode::g2poly::{G2Poly, gcd};
/// let a = G2Poly(0b11011);
/// let b = G2Poly(0b100001);
/// assert_eq!(gcd(a, b), G2Poly(0b11));
/// assert_eq!(gcd(b, a), G2Poly(0b11));
/// ```
pub fn gcd(a: G2Poly, b: G2Poly) -> G2Poly {
    let (mut a, mut b) = (cmp::max(a, b), cmp::min(a, b));

    while b != G2Poly(0) {
        let new_b = a % b;
        a = b;
        b = new_b;
    }
    a
}

/// Calculate the greatest common divisor with Bézout coefficients
///
/// Uses the extended euclidean algorithm to calculate the greatest common divisor of two
/// polynomials. Also returns the Bézout coefficients x and y such that
/// > gcd(a, b) == a * x + b * x
///
/// # Example
/// ```rust
/// use qr_code::decode::g2poly::{G2Poly, extended_gcd};
///
/// let a = G2Poly(0b11011);
/// let b = G2Poly(0b100001);
/// let (gcd, x, y) = extended_gcd(a, b);
/// assert_eq!(gcd, G2Poly(0b11));
/// assert_eq!((a * x).to_poly() + (b * y).to_poly(), G2Poly(0b11));
/// ```
pub fn extended_gcd(a: G2Poly, b: G2Poly) -> (G2Poly, G2Poly, G2Poly) {
    let mut s = G2Poly(0);
    let mut old_s = G2Poly(1);
    let mut t = G2Poly(1);
    let mut old_t = G2Poly(0);
    let mut r = b;
    let mut old_r = a;

    while r != G2Poly(0) {
        let quotient = old_r / r;
        let tmp = old_r - (quotient * r).to_poly();
        old_r = r;
        r = tmp;

        let tmp = old_s - (quotient * s).to_poly();
        old_s = s;
        s = tmp;

        let tmp = old_t - (quotient * t).to_poly();
        old_t = t;
        t = tmp;
    }

    (old_r, old_s, old_t)
}

impl G2Poly {
    /// The constant `1` polynomial.
    ///
    /// This is the multiplicative identity. (a * UNIT = a)
    pub const UNIT: Self = G2Poly(1);
    /// The constant `0 polynomial`
    ///
    /// This is the additive identity (a + ZERO = a)
    pub const ZERO: Self = G2Poly(0);

    /// The `x` polynomial.
    ///
    /// Useful for quickly generating `x^n` values.
    pub const X: Self = G2Poly(2);

    /// Quickly calculate p^n mod m
    ///
    /// Uses [square-and-multiply](https://en.wikipedia.org/wiki/Exponentiation_by_squaring) to
    /// quickly exponentiate a polynomial.
    ///
    /// # Example
    /// ```rust
    /// use qr_code::decode::g2poly::G2Poly;
    /// let p = G2Poly(0b1011);
    /// assert_eq!(p.pow_mod(127, G2Poly(0b1101)), G2Poly(0b110));
    /// ```
    pub fn pow_mod(self, power: u64, modulus: G2Poly) -> G2Poly {
        let mut init = G2Poly::UNIT;

        // max starts with only the highest bit set
        let mut max = 0x80_00_00_00_00_00_00_00;
        assert_eq!(max << 1, 0);

        while max > 0 {
            let square = init * init;
            init = square % modulus;
            if power & max > 0 {
                let mult = init * self;
                init = mult % modulus;
            }
            max >>= 1;
        }
        init
    }

    /// Determine if the given polynomial is irreducible.
    ///
    /// Irreducible polynomials not be expressed as the product of other irreducible polynomials
    /// (except `1` and itself). This uses [Rabin's tests](https://en.wikipedia.org/wiki/Factorization_of_polynomials_over_finite_fields#Rabin's_test_of_irreducibility)
    /// to check if the given polynomial is irreducible.
    ///
    /// # Example
    /// ```rust
    /// use qr_code::decode::g2poly::G2Poly;
    /// let p = G2Poly(0b101);
    /// assert!(!p.is_irreducible()); // x^2 + 1 == (x + 1)^2 in GF(2)
    /// let p = G2Poly(0b111);
    /// assert!(p.is_irreducible());
    /// ```
    pub fn is_irreducible(self) -> bool {
        const PRIMES_LE_63: [u64; 11] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31];

        // Zero is not irreducible
        if self == G2Poly::ZERO {
            return false;
        }

        // Degrees
        let n = self.degree().expect("Already checked for zero");
        let distinct_prime_coprod = PRIMES_LE_63
            .iter()
            .filter(|&&p| p <= n)
            .filter(|&&p| n % p == 0)
            .map(|&p| n / p);
        for p in distinct_prime_coprod {
            let q_to_the_p = 1 << p;
            let h = G2Poly::X.pow_mod(q_to_the_p, self) - (G2Poly(2) % self);

            if gcd(self, h) != G2Poly(1) {
                return false;
            }
        }

        let g = G2Poly::X.pow_mod(1 << n, self) - G2Poly(2) % self;

        g == G2Poly::ZERO
    }

    /// Get the degree of the polynomial
    ///
    /// Returns `None` for the 0 polynomial (which has degree `-infinity`),
    /// otherwise is guaranteed to return `Some(d)` with `d` the degree.
    ///
    /// ```rust
    /// use qr_code::decode::g2poly::G2Poly;
    /// let z = G2Poly::ZERO;
    /// assert_eq!(z.degree(), None);
    /// let s = G2Poly(0b101);
    /// assert_eq!(s.degree(), Some(2));
    /// ```
    pub fn degree(self) -> Option<u64> {
        63_u32.checked_sub(self.0.leading_zeros()).map(|n| n as u64)
    }

    /// Checks if a polynomial generates the multiplicative group mod m.
    ///
    /// The field GF(2^p) can be interpreted as all polynomials of degree < p, with all operations
    /// carried over from polynomials. Multiplication is done mod m, where m is some irreducible
    /// polynomial of degree p. The multiplicative group is cyclic, so there is an element `a` so
    /// that all elements != can be expressed as a^n for some n < 2^p - 1.
    ///
    /// This checks if the given polynomial is such a generator element mod m.
    ///
    /// # Example
    /// ```rust
    /// use qr_code::decode::g2poly::G2Poly;
    /// let m = G2Poly(0b10011101);
    /// // The element `x` generates the whole group.
    /// assert!(G2Poly::X.is_generator(m));
    /// ```
    pub fn is_generator(self, module: G2Poly) -> bool {
        assert!(module.is_irreducible());

        let order = module.degree().expect("Module is not 0");
        let p_minus_1 = (1 << order) - 1;

        let mut g_pow = self;
        for _ in 1..p_minus_1 {
            if g_pow == G2Poly::UNIT {
                return false;
            }

            g_pow = (g_pow * self) % module;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_debug_format() {
        let a = 0;
        let b = 0b0110;
        let c = 1;
        let d = 49;

        assert_eq!(format!("{:?}", G2Poly(a)), "G2Poly { 0 }");
        assert_eq!(format!("{:?}", G2Poly(b)), "G2Poly { 110 }");
        assert_eq!(format!("{:?}", G2Poly(c)), "G2Poly { 1 }");
        assert_eq!(format!("{:?}", G2Poly(d)), "G2Poly { 110001 }");
    }

    #[test]
    fn test_display_format() {
        let a = 0;
        let b = 0b0110;
        let c = 1;
        let d = 49;

        assert_eq!(format!("{}", G2Poly(a)), "G2Poly { 0 }");
        assert_eq!(format!("{}", G2Poly(b)), "G2Poly { x^2 + x }");
        assert_eq!(format!("{}", G2Poly(c)), "G2Poly { 1 }");
        assert_eq!(format!("{}", G2Poly(d)), "G2Poly { x^5 + x^4 + 1 }");
    }

    #[test]
    fn test_poly_prod() {
        let e = G2Poly(1);
        let a = G2Poly(0b01101);
        let b = G2Poly(0b11111);
        let c = G2Poly(0xff_ff_ff_ff_ff_ff_ff_ff);

        assert_eq!(e * e, G2PolyProd(1));
        assert_eq!(a * e, G2PolyProd(0b01101));
        assert_eq!(b * e, G2PolyProd(0b11111));
        assert_eq!(c * e, G2PolyProd(0xff_ff_ff_ff_ff_ff_ff_ff));
        assert_eq!(a * b, G2PolyProd(0b10011011));
        assert_eq!(
            a * c,
            G2PolyProd(0b1001111111111111111111111111111111111111111111111111111111111111011)
        );
        assert_eq!(c * c, G2PolyProd(0b1010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101));
    }

    #[test]
    fn test_poly_rem() {
        let a = G2PolyProd(0b00111);
        let b = G2PolyProd(0b10101);
        let m = G2Poly(0b01001);

        assert_eq!(a % m, G2Poly(0b00111));
        assert_eq!(b % m, G2Poly(0b0111));
    }

    #[test]
    fn test_irreducible_check() {
        let a = G2Poly(0b11);
        let b = G2Poly(0b1101);
        let c = G2Poly(0x80_00_00_00_80_00_00_01);

        let z = G2Poly(0b1001);
        let y = G2Poly(0x80_00_00_00_80_00_00_03);

        assert!(a.is_irreducible());
        assert!(b.is_irreducible());
        assert!(c.is_irreducible());
        assert!(!z.is_irreducible());
        assert!(!y.is_irreducible());
    }

    #[test]
    fn test_generator_check() {
        // Rijndael's field
        let m = G2Poly(0b100011011);
        let g = G2Poly(0b11);

        assert!(g.is_generator(m));
    }

    #[test]
    #[should_panic]
    fn test_generator_check_fail() {
        let m = G2Poly(0b101);
        let g = G2Poly(0b1);

        g.is_generator(m);
    }

    #[test]
    fn test_poly_div() {
        let a = G2Poly(0b10000001001);
        let b = G2Poly(0b1010);

        assert_eq!(G2Poly(0b10101011), a / b);
    }

    #[test]
    fn test_extended_euclid() {
        let m = G2Poly(0b10000001001);
        let a = G2Poly(10);

        let (gcd, x, _) = extended_gcd(a, m);
        assert_eq!(G2Poly(1), gcd);
        assert_eq!(G2Poly(1), a * x % m);
    }
}
