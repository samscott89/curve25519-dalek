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

use core::ops::Add;
use core::ops::Neg;
use core::ops::Sub;

use curve::ExtendedPoint;
use curve::CompressedMontgomeryX;
use field::FieldElement;
use scalar::Scalar;
use subtle::CTAssignable;

use constants::A;


/// A uniform representative of a point.
pub struct UniformRepresentative(FieldElement);

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

/// Map a `point` to its uniform representative value (i.e. a uniformly random
/// string).
///
/// # Return
///
/// A `UniformRepresentative` encoding of the `point`.
pub fn elligator2(X: &FieldElement) -> UniformRepresentative {
    let one:    FieldElement = FieldElement::one();
    let n:      FieldElement = FieldElement([2, 0, 0, 0, 0, 0, 0, 0, 0, 0]); // n = 2
    let nrr:    FieldElement = &n * &X.square();                             // nr²
    let mut u:  FieldElement = &(-(&A)) * &(&one + &nrr).invert();           // u = -A/(1 + nr²)
    let w:      FieldElement = &u * &(&(&u.square() + &(&A * &u)) + &one);   // w = u(u² + Au + 1)
    let uprime: FieldElement = &(-(&A)) - &u;

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

    UniformRepresentative(u)
}

pub fn decode(representative: &UniformRepresentative) -> ExtendedPoint {
    unimplemented!()
}


#[cfg(test)]
mod test {

}
