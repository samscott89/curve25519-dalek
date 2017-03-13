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
use constants::HALF_Q_MINUS_1_BYTES;
use constants::SQRT_M1;
use constants::SQRT_MINUS_HALF;
use field::FieldElement;
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
    pub fn from_bytes(bytes: &[u8; 32]) -> UniformRepresentative {
        UniformRepresentative(FieldElement::from_bytes(bytes))
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
        /// u = -A/(1 + nr²);   w = u(u² + Au + 1);   u' = -(A+u);
        //let (mut u, w, uprime) = UniformRepresentative::elligator2(&point.X);
        //let nonsquare: u8 = legendre_is_nonsquare(&w);
        //if nonsquare == 0 { return None; }
        /// If w is non-square, then we recompute u to be u' = -A - u:
        //u.conditional_assign(&uprime, nonsquare);
        //Some(UniformRepresentative(u))

        //let a:     ExtendedPoint = ExtendedPoint::basepoint_mult(&Scalar(self.masked()));
        let inv:   FieldElement  = (&(&point.Z - &point.Y) * &point.X).invert();  // 1/XZ-XY
        let mut t: FieldElement  = &point.Y + &point.Z;        // Y+Z
        let u:     FieldElement  = &(&inv * &point.X) * &t;    // (X/X(Z-Y))*(Y+Z) == (Y+Z)/(Z-Y)

        //let a:   ExtendedGroupElement = curve::scalar_mult_base(&Scalar(point.as_bytes()));
        //let inv: FieldElement         = ((a.Z - a.Y) * a.X).invert();  // 1/XZ-XY
        //let mut t: FieldElement = a.Y + a.Z;       // Y+Z
        //let u:     FieldElement = (inv * a.X) * t; // (X/X(Z-Y))*(Y+Z) == (Y+Z)/(Z-Y)

        let v:     FieldElement  = &inv * &t;                  // Y+Z/XZ-XY

        let b:     FieldElement  = &u + &A;
        let b3:    FieldElement  = &b.square() * &b;  // b^3
        let mut c: FieldElement  = &b3.square() * &b; // b^7  // XXX reuse
        let b8:    FieldElement  = &c * &b;           // b^8
        c    = c.pow_p58();                           // b^(7*(p-5)/8)

        let mut chi: FieldElement = c.square();       // b^(14*(p-5)/8)
        chi  = &chi.square() * &u.square();           // b^(28*(p-5)/8)
        t    = &b3.square() * &b;                     // b^7  // XXX reuse here
        t    = t.square();                            // b^14;
        chi *= &t;
        chi  = -(&chi);

        // chi[1] is either 0 or 0xFF
        if chi.to_bytes()[1] == 0xFF { return None; }

        // Calculate r1 == sqrt(-u/(2*(u+A)))
        let mut r1: FieldElement = &(&(&c * &u) * &b3) * &SQRT_MINUS_HALF;

        t  = &r1.square() * &b; // XXX combine
        t += &(&t + &u);

        let mut maybe_sqrt_m1: FieldElement = FieldElement::one();
        maybe_sqrt_m1.conditional_assign(&SQRT_M1, t.is_nonzero());
        r1 *= &maybe_sqrt_m1;  // XXX make conditional_mult() ?

        // Calculate r = sqrt(-(u+A)/(2u))
        let mut r: FieldElement;
        t  = &c.square() * &c;    // (b^(7*(p-5)/8)) ^3  // XXX combine with next line
        t  = t.square();          // (b^(7*(p-5)/8)) ^6
        r  = &t * &c;             // (b^(7*(p-5)/8)) ^7
        t  = &u.square() * &u;    // (Y+Z)/(Z-Y) ^3
        r *= &t;
        t  = &(&b8.square() * &b8) * &b;  // b^25
        r *= &(&t * &SQRT_MINUS_HALF);
        t  = &(&r.square() * &u) + &(&t + &b);

        maybe_sqrt_m1 = FieldElement::one();
        maybe_sqrt_m1.conditional_assign(&SQRT_M1, t.is_nonzero());
        r *= &maybe_sqrt_m1;

        let v_in_square_root_image: u8 = v.bytes_equal_less_than(&HALF_Q_MINUS_1_BYTES);
        r.conditional_assign(&r1, v_in_square_root_image);

        Some(UniformRepresentative(r))
    }

    /// Decode this `UniformRepresentative` into an `ExtendedPoint`.
    ///
    /// # Return
    ///
    /// An `ExtendedPoint`.
    pub fn decode(&self) -> Option<ExtendedPoint> {  // RepresentativeToPublicKey
        let mut v: FieldElement;
        let mut v2: FieldElement;
        let v3: FieldElement;
        let mut e: FieldElement;

        // From r = sqrt(-(u+A)/(2u)), calculate 2r² = -(u+A)/(u):
        let mut rr2: FieldElement = self.0;
        rr2 = rr2.square2();
        rr2[0] += 1;
        rr2 = rr2.invert();

        v   = -&(&A * &rr2); // (-Au - A²)/u
        v2  = v.square();    // (A²u² + 2A³u + A⁴)/u²
        v3  = &v * &v2;      // (-2A⁶ - 4A⁴u² - A³u³ - A³u)/u³
        e   = &v3 + &v;      // (-2A⁶ - 4A⁴u² - A³u³ - A³u)/u³ + (-Au - A²)/u
        v2 *= &A;            // (A³u² + 2A⁴u + A⁵)/u²
        e  += &v2;           // (-2A⁶ - 4A⁴u² - A³u³ - A³u)/u³ + (-Au - A²)/u + (A³u² + 2A⁴u + A⁵)/u²
        e   = e.chi();       // oh god

        // e.to_bytes[1] is either 0 (for e = 1) or 0xff (for e = -1)
        let e_is_minus_one: u8 = e.to_bytes()[1] & 1;
        let minus_v: FieldElement = -&v;

        v.conditional_assign(&minus_v, e_is_minus_one);
        v2 = FieldElement::zero();
        v2.conditional_assign(&A, e_is_minus_one);
        v -= &v2;            // Y+Z/XZ-XY ??

        CompressedMontgomeryU(v.to_bytes()).decompress() // XXX this is not the original u?
    }

    /*
    /// Decode this `UniformRepresentative` into an `ExtendedPoint`.
    ///
    /// # Return
    ///
    /// An `ExtendedPoint`.
    pub fn decode(&self) -> Option<ExtendedPoint> {
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

        CompressedMontgomeryU(u.to_bytes()).decompress()
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
    */
}

#[cfg(test)]
mod test {
    use test::Bencher;
    use rand::OsRng;

    use constants::BASE_CMPRSSD;
    use constants::BASEPOINT;
    use curve::BasepointMult;
    use curve::CompressedEdwardsY;
    use curve::ExtendedPoint;
    use curve::ScalarMult;
    use field::FieldElement;//xxx
    use scalar::Scalar;

    use super::*;

    #[test]
    fn roundtrip() {
        let u: UniformRepresentative = UniformRepresentative::encode(&BASEPOINT).unwrap();
        let r: ExtendedPoint = u.decode().unwrap();

        assert_eq!(BASE_CMPRSSD, r.compress_edwards());
    }

    #[test]
    fn random_roundtrip() {
        let mut rng: OsRng = OsRng::new().unwrap();
        let mut p: Option<ExtendedPoint> = None;
        let mut u: Option<UniformRepresentative> = None;
        let r: ExtendedPoint;

        while u.is_none() {
            p = Some(ExtendedPoint::basepoint_mult(&Scalar::random(&mut rng)));
            u = UniformRepresentative::encode(&p.unwrap());
        }
        r = u.unwrap().decode().unwrap();

        assert_eq!(p.unwrap().compress_edwards(), r.compress_edwards());
    }

    #[test]
    fn encode() {
        let u: Option<UniformRepresentative> = UniformRepresentative::encode(&BASEPOINT);

        assert!(u.is_some())
    }

    #[test]
    fn decode() {
        let u: UniformRepresentative = UniformRepresentative::encode(&BASEPOINT).unwrap();
        let r: Option<ExtendedPoint> = u.decode();

        assert!(r.is_some())
    }

    #[test]
    fn matches_extra25519_go() {
        let public_key_1: ExtendedPoint = CompressedMontgomeryU(
            [ 235, 026, 152, 083, 081, 164, 166, 007,
              202, 028, 004, 108, 062, 045, 008, 248,
              142, 166, 036, 139, 028, 058, 216, 129,
              216, 122, 213, 057, 004, 229, 001, 096, ]).decompress().unwrap();
        let public_key_2: ExtendedPoint = CompressedMontgomeryU(
            [ 149, 048, 143, 208, 141, 151, 014, 105,
              167, 248, 103, 068, 153, 164, 072, 161,
              092, 027, 228, 022, 255, 000, 007, 172,
              117, 201, 036, 039, 072, 106, 050, 113, ]).decompress().unwrap();
        let public_key_3: ExtendedPoint = CompressedMontgomeryU(
            [ 127, 077, 036, 085, 205, 165, 206, 063,
              146, 083, 124, 108, 116, 044, 000, 015,
              017, 024, 119, 039, 247, 114, 249, 216,
              118, 011, 093, 060, 072, 208, 247, 062, ]).decompress().unwrap();
        let public_key_4: ExtendedPoint = CompressedMontgomeryU(
            [ 063, 058, 107, 008, 072, 244, 192, 219,
              194, 148, 154, 034, 200, 003, 210, 153,
              227, 194, 138, 197, 213, 108, 132, 036,
              165, 128, 067, 028, 074, 145, 144, 108, ]).decompress().unwrap();
        let represent_1: UniformRepresentative = UniformRepresentative::from_bytes(&
            [ 207, 143, 081, 022, 139, 031, 245, 212,
              254, 182, 088, 095, 189, 181, 102, 130,
              187, 180, 114, 176, 111, 168, 115, 087,
              192, 030, 171, 110, 032, 099, 134, 111, ]);
        let represent_2: UniformRepresentative = UniformRepresentative::from_bytes(&
            [ 025, 095, 127, 153, 194, 020, 212, 144,
              122, 078, 073, 045, 171, 155, 215, 170,
              154, 060, 040, 227, 153, 194, 050, 200,
              215, 001, 185, 163, 206, 251, 160, 058, ]);
        let represent_3: UniformRepresentative = UniformRepresentative::from_bytes(&
            [ 129, 054, 240, 155, 063, 150, 152, 143,
              093, 085, 073, 177, 242, 216, 177, 250,
              237, 021, 056, 044, 129, 253, 031, 185,
              090, 057, 025, 186, 007, 028, 203, 102, ]);
        let represent_4: UniformRepresentative = UniformRepresentative::from_bytes(&
            [ 059, 090, 002, 048, 029, 013, 052, 013,
              247, 070, 035, 124, 237, 010, 076, 180,
              239, 069, 019, 001, 069, 005, 184, 098,
              221, 201, 143, 198, 225, 203, 248, 078, ]);

        assert_eq!(UniformRepresentative::encode(&public_key_1).unwrap(), represent_1);

    }

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

    #[bench]
    fn encode(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let p: ExtendedPoint = ExtendedPoint::basepoint_mult(&Scalar::random(&mut rng));

        b.iter(| | UniformRepresentative::encode(&p) )
    }

    #[bench]
    fn decode(b: &mut Bencher) {
        let mut rng: OsRng = OsRng::new().unwrap();
        let mut p: ExtendedPoint;
        let mut u: Option<UniformRepresentative>;
        let r: UniformRepresentative;

        loop {
            p = ExtendedPoint::basepoint_mult(&Scalar::random(&mut rng));
            u = UniformRepresentative::encode(&p);

            if u.is_some() {
                r = u.unwrap();
                break;
            }
        }

        b.iter(| | r.decode() )
    }
}
