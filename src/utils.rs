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

//! Miscellaneous common utility functions.

/// Convert an array of (at least) three bytes into an i64.
#[inline]
//#[allow(dead_code)]
pub fn load3(input: &[u8]) -> i64 {
       (input[0] as i64)
    | ((input[1] as i64) << 8)
    | ((input[2] as i64) << 16)
}

/// Convert an array of (at least) four bytes into an i64.
#[inline]
//#[allow(dead_code)]
pub fn load4(input: &[u8]) -> i64 {
       (input[0] as i64)
    | ((input[1] as i64) << 8)
    | ((input[2] as i64) << 16)
    | ((input[3] as i64) << 24)
}

/// "Clamp" an array of 32 bytes.
///
/// No one really know why we do "key clamping".  There are, however, some
/// plausible theories.
///
/// Purportedly, the lower three bits are cleared to elliminate the cofactor
/// for secret keys by ensuring that the key is always 0 mod 8, in order to
/// reduce potential active, small subgroup attacks on key exchanges.
///
/// Additionally, bit 254 is set, in order to avoid timing side-channels in
/// hypothetical, idiotic Montgomery Ladder implementations.  Since those who
/// set this bit should also be sufficiently capable of implementing
/// side-channel resistant Montgomery Ladders, setting this bit could be
/// likened to joining a circle jerk of people who are marking themselves as
/// Doing It Right—just in case—so that if there ever comes a day when someone
/// is Doing It Wrong, they can all stop jerking each other off and stare at
/// That Guy and then wank each other off some more in celebration of not
/// being That Guy.
///
/// The primary use for this function is backwards compatibility with legacy
/// (reference) code.
#[inline(always)]
pub fn clamp(bytes: &mut [u8; 32]) {
    bytes[0]  &= 248;
    bytes[31] &= 127;
    bytes[31] |= 64;
}
