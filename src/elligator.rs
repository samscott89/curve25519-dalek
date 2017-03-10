// -*- mode: rust; -*-
//
// To the extent possible under law, the authors have waived all copyright and
// related or neighboring rights to curve25519-dalek, using the Creative
// Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/.0/> for full details.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Hashing to a point on the curve and uniform representations of points.
//!
//! This module implements the elligator2 encoding described in ["Elligator:
//! Elliptic Curve Points Indistinguishable From Random
//! Strings"](https://elligator.cr.yp.to/elligator-20130828.pdf)
//!
//! The elligator2 encoding is a bijective map between uniformly random strings
//! and roughly half of the points on a curve.  It is suitable for use with any
//! elliptic curve with a point `(0, 0)` of order 2, and whose j-invariant is
//! not 1728.  Namely, it is suitable for curve25519.
//!
//! Because only half of the curve points are contained within the bijective
//! map, encoding a curve point to its uniform representation will fail with
//! probability roughly P(0.5).  Hence, on average, to obtain a uniform
//! representation of a random curve point, one will need to conduct the
//! encoding with [XXX function name] twice.  To simply obtain a random curve
//! point and its uniform representation without failures, call [XXX function
//! name].

use curve::ExtendedPoint;
use curve::CompressedMontgomeryU;
use constants::A;
use field::FieldElement;
use scalar::Scalar;
use subtle::CTAssignable;


/// Determine if a `FieldElement`, `x` is square by computing its Legendre
/// symbol, `x^((p-1)/2)`.
///
/// # Return
///
/// Returns `1u8` if `x` is non-square, and `0u8` if it is either zero or a
/// square.
fn legendre_is_nonsquare(x: &FieldElement) -> u8 {
    // non-zero square →  1
    // zero            →  0
    // non-square      → -1
    let legendre_is_square: i8 = x.chi().0[0] as i8;

    // (1 ^ legendre_is_square) >> 7 will be 0 if legendre_is_square is either
    // 1 or 0, and -1 otherwise, so we just flip the sign.
    (-(1i8 ^ legendre_is_square) >> 7i8) as u8
}

/// A uniform representative of a point.
pub struct UniformRepresentative(FieldElement);

impl UniformRepresentative {
    /// Convert this `UniformRepresentative` as an array of 32 bytes.
    ///
    /// # Return
    ///
    /// A `[u8; 32]`.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }

    /// Construct a `UniformRepresentative` from some bytes.
    ///
    /// Convert the `bytes` to a `FieldElement` and use it to construct a
    /// `UniformRepresentative`.  (Recall that all random strings of 32 bytes in
    /// length represent a valid point on the curve.  However, the converse is
    /// not true.)
    ///
    /// # Warning
    ///
    /// The `bytes` must be _uniformly random_, e.g. the output of a suitable
    /// PRF.  The `bytes` must also be _at least_ 32 bytes in length.
    ///
    /// # Return
    ///
    /// A `UniformRepresentative` of a point on the curve.
    pub fn from_bytes(bytes: &[u8]) -> UniformRepresentative {
        debug_assert!(bytes.len() >= 32);

        let data: &[u8; 32]    = array_ref!(bytes, 0, 32);
        let fe:   FieldElement = FieldElement::from_bytes(data);

        UniformRepresentative(fe)
    }

    /// Map a `point` to its uniform representative value (i.e. a uniformly random
    /// string).
    ///
    /// # Warning
    ///
    /// This function is _not_ constant-time.  We don't care, for the reason
    /// that—if your point fails to encode to its representative form in your
    /// protocol—your protocol likely needs to behave differently than it would
    /// if encoding had succeeded, i.e. choose a new point, etc.
    ///
    /// # Return
    ///
    /// A `UniformRepresentative` encoding of the `point`.
    pub fn encode(point: &ExtendedPoint) -> Option<UniformRepresentative> {
        // u = -A/(1 + nr²);   w = u(u² + Au + 1);   u' = -(A+u);
        let (mut u, w, uprime) = UniformRepresentative::elligator2(&point.X);

        let nonsquare: u8 = legendre_is_nonsquare(&w);

        if nonsquare == 0 {
            return None;
        }
        // If w is non-square, then we recompute u to be u' = -A - u:
        u.conditional_assign(&uprime, nonsquare);

        Some(UniformRepresentative(u))
    }

    /// Decode this `UniformRepresentative` into an `ExtendedPoint`.
    ///
    /// # Return
    ///
    /// An `ExtendedPoint`.
    pub fn decode(&self) -> CompressedMontgomeryU {
        let r: FieldElement = FieldElement::from_bytes(&self.to_bytes());

        // u = -A/(1 + nr²);   w = u(u² + Au + 1);   u' = -(A+u);
        let (mut u, w, uprime) = UniformRepresentative::elligator2(&r);

        // If u and u' are integers modulo p such that u' = -A - u and u/u' = nr²
        // for any r and fixed nonsquare n, then the Montgomery curve equation
        // v = u(u² + Au + 1) has a solution for u = u or u = u', or both.
        //
        // From the above lemma, it follows that u = -A/(1 + nr²) and
        // u' = -Anr²/(1 + nr²). Thus, given r, we can easily calculate u and u' and
        // use the Legendre symbol to choose whichever value gives a square w.
        let nonsquare: u8 = legendre_is_nonsquare(&w);

        // If w is non-square, then we recompute u to be u' = -A - u:
        u.conditional_assign(&uprime, nonsquare);

        CompressedMontgomeryU(u.to_bytes())
    }

    /// # Return
    ///
    /// A tripel of `FieldElement`s: `(u, w, u')`
    fn elligator2(r: &FieldElement) -> (FieldElement, FieldElement, FieldElement) {
        let one:    FieldElement = FieldElement::one();
        let n:      FieldElement = FieldElement([2, 0, 0, 0, 0, 0, 0, 0, 0, 0]); // n = 2
        let nrr:    FieldElement = &n * &r.square();                             // nr²
        let u:      FieldElement = &(-(&A)) * &(&one + &nrr).invert();           // u = -A/(1 + nr²)
        let w:      FieldElement = &u * &(&(&u.square() + &(&A * &u)) + &one);   // w  = u(u² + Au + 1)
        let uprime: FieldElement = &(-(&A)) - &u;                                // u' = -(A+2)

        (u, w, uprime)
    }
}

#[cfg(test)]
mod test {
    use test::Bencher;
    use rand::OsRng;

    use curve::BasepointMult;
    use curve::ExtendedPoint;
    use curve::ScalarMult;
    use field::FieldElement;//xxx
    use scalar::Scalar;

    use super::*;

    #[test]
    fn random_roundtrip() {
        let mut rng: OsRng = OsRng::new().unwrap();
        let mut p: Option<ExtendedPoint> = None;
        let mut u: Option<UniformRepresentative> = None;
        let r: CompressedMontgomeryU;

        while u.is_none() {
            p = Some(ExtendedPoint::basepoint_mult(&Scalar::random(&mut rng)));
            //u = UniformRepresentative::encode(&p);
            u = Some(UniformRepresentative(FieldElement::one()));
        }
        r = u.unwrap().decode();

        assert_eq!(p.unwrap().compress_montgomery().unwrap(), r);
    }

    // #[test]
    // fn encode() {
    //     let mut rng: OsRng = OsRng::new().unwrap();
    //     let p: ExtendedPoint = ExtendedPoint::basepoint_mult(&Scalar::random(&mut rng));
    //     
    //     UniformRepresentative::encode(&p);
    // }
    // 
    // #[test]
    // fn decode() {
    //     let mut rng: OsRng = OsRng::new().unwrap();
    //     let mut p: ExtendedPoint;
    //     let mut u: Option<UniformRepresentative>;
    //     let r: CompressedMontgomeryU;
    // 
    //     loop {
    //         p = ExtendedPoint::basepoint_mult(&Scalar::random(&mut rng));
    //         u = UniformRepresentative::encode(&p);
    // 
    //         if u.is_some() {
    //             r = u.unwrap().decode();
    //             break;
    //         }
    //     }
    // }
}

#[cfg(test)]
mod bench {
    use test::Bencher;
    use rand::OsRng;

    use curve::BasepointMult;
    use curve::ExtendedPoint;
    use curve::ScalarMult;
    use scalar::Scalar;

    use super::*;

    // #[bench]
    // fn encode(b: &mut Bencher) {
    //     let mut rng: OsRng = OsRng::new().unwrap();
    //     let p: ExtendedPoint = ExtendedPoint::basepoint_mult(&Scalar::random(&mut rng));
    //     
    //     b.iter(| | UniformRepresentative::encode(&p) )
    // }
    // 
    // #[bench]
    // fn decode(b: &mut Bencher) {
    //     let mut rng: OsRng = OsRng::new().unwrap();
    //     let mut p: ExtendedPoint;
    //     let mut u: Option<UniformRepresentative>;
    //     let r: UniformRepresentative;
    // 
    //     loop {
    //         p = ExtendedPoint::basepoint_mult(&Scalar::random(&mut rng));
    //         u = UniformRepresentative::encode(&p);
    // 
    //         if u.is_some() {
    //             r = u.unwrap();
    //             break;
    //         }
    //     }
    // 
    //     b.iter(| | r.decode() )
    // }
}
