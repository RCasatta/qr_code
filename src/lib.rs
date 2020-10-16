//!
//! qr_code
//!
//! This crate provides a [QrCode](crate::QrCode) encoder and decoder
//!

#![deny(missing_docs)]
#![deny(warnings)]
#![allow(
    clippy::must_use_candidate, // This is just annoying.
    clippy::use_self, // Rust 1.33 doesn't support Self::EnumVariant, let's try again in 1.37.
    clippy::match_like_matches_macro, // MSRV is lower than what's needed for matches!
)]
#![cfg_attr(feature = "bench", doc(include = "../README.md"))]
// ^ make sure we can test our README.md.

// Re-exported dependencies.
#[cfg(feature = "bmp")]
pub extern crate bmp_monochrome;

use std::ops::Index;

pub mod bits;
pub mod canvas;
mod cast;
pub mod ec;
pub mod optimize;
mod render;
pub mod types;

#[cfg(feature = "bmp")]
pub mod decode;

pub use crate::types::{Color, EcLevel, QrResult, Version};

use crate::cast::As;

/// The encoded QR code symbol.
#[derive(Clone)]
pub struct QrCode {
    content: Vec<Color>,
    version: Version,
    ec_level: EcLevel,
    width: usize,
}

impl QrCode {
    /// Constructs a new QR code which automatically encodes the given data.
    ///
    /// This method uses the "medium" error correction level and automatically
    /// chooses the smallest QR code.
    ///
    ///     use qr_code::QrCode;
    ///
    ///     let code = QrCode::new(b"Some data").unwrap();
    ///
    /// # Errors
    ///
    /// Returns error if the QR code cannot be constructed, e.g. when the data
    /// is too long.
    pub fn new<D: AsRef<[u8]>>(data: D) -> QrResult<Self> {
        Self::with_error_correction_level(data, EcLevel::M)
    }

    /// Constructs a new QR code which automatically encodes the given data at a
    /// specific error correction level.
    ///
    /// This method automatically chooses the smallest QR code.
    ///
    ///     use qr_code::{QrCode, EcLevel};
    ///
    ///     let code = QrCode::with_error_correction_level(b"Some data", EcLevel::H).unwrap();
    ///
    /// # Errors
    ///
    /// Returns error if the QR code cannot be constructed, e.g. when the data
    /// is too long.
    pub fn with_error_correction_level<D: AsRef<[u8]>>(
        data: D,
        ec_level: EcLevel,
    ) -> QrResult<Self> {
        let bits = bits::encode_auto(data.as_ref(), ec_level)?;
        Self::with_bits(bits, ec_level)
    }

    /// Constructs a new QR code for the given version and error correction
    /// level.
    ///
    ///     use qr_code::{QrCode, Version, EcLevel};
    ///
    ///     let code = QrCode::with_version(b"Some data", Version::Normal(5), EcLevel::M).unwrap();
    ///
    /// This method can also be used to generate Micro QR code.
    ///
    ///     use qr_code::{QrCode, Version, EcLevel};
    ///
    ///     let micro_code = QrCode::with_version(b"123", Version::Micro(1), EcLevel::L).unwrap();
    ///
    /// # Errors
    ///
    /// Returns error if the QR code cannot be constructed, e.g. when the data
    /// is too long, or when the version and error correction level are
    /// incompatible.
    pub fn with_version<D: AsRef<[u8]>>(
        data: D,
        version: Version,
        ec_level: EcLevel,
    ) -> QrResult<Self> {
        let mut bits = bits::Bits::new(version);
        bits.push_optimal_data(data.as_ref())?;
        bits.push_terminator(ec_level)?;
        Self::with_bits(bits, ec_level)
    }

    /// Constructs a new QR code with encoded bits.
    ///
    /// Use this method only if there are very special need to manipulate the
    /// raw bits before encoding. Some examples are:
    ///
    /// * Encode data using specific character set with ECI
    /// * Use the FNC1 modes
    /// * Avoid the optimal segmentation algorithm
    ///
    /// See the `Bits` structure for detail.
    ///
    ///     #![allow(unused_must_use)]
    ///
    ///     use qr_code::{QrCode, Version, EcLevel};
    ///     use qr_code::bits::Bits;
    ///
    ///     let mut bits = Bits::new(Version::Normal(1));
    ///     bits.push_eci_designator(9);
    ///     bits.push_byte_data(b"\xca\xfe\xe4\xe9\xea\xe1\xf2 QR");
    ///     bits.push_terminator(EcLevel::L);
    ///     let qrcode = QrCode::with_bits(bits, EcLevel::L);
    ///
    /// # Errors
    ///
    /// Returns error if the QR code cannot be constructed, e.g. when the bits
    /// are too long, or when the version and error correction level are
    /// incompatible.
    pub fn with_bits(bits: bits::Bits, ec_level: EcLevel) -> QrResult<Self> {
        let version = bits.version();
        let data = bits.into_bytes();
        let (encoded_data, ec_data) = ec::construct_codewords(&*data, version, ec_level)?;
        let mut canvas = canvas::Canvas::new(version, ec_level);
        canvas.draw_all_functional_patterns();
        canvas.draw_data(&*encoded_data, &*ec_data);
        let canvas = canvas.apply_best_mask();
        Ok(Self {
            content: canvas.into_colors(),
            version,
            ec_level,
            width: version.width().as_usize(),
        })
    }

    /// Gets the version of this QR code.
    pub fn version(&self) -> Version {
        self.version
    }

    /// Gets the error correction level of this QR code.
    pub fn error_correction_level(&self) -> EcLevel {
        self.ec_level
    }

    /// Gets the number of modules per side, i.e. the width of this QR code.
    ///
    /// The width here does not contain the quiet zone paddings.
    pub fn width(&self) -> usize {
        self.width
    }

    /// Gets the maximum number of allowed erratic modules can be introduced
    /// before the data becomes corrupted. Note that errors should not be
    /// introduced to functional modules.
    pub fn max_allowed_errors(&self) -> usize {
        ec::max_allowed_errors(self.version, self.ec_level).expect("invalid version or ec_level")
    }

    /// Checks whether a module at coordinate (x, y) is a functional module or
    /// not.
    pub fn is_functional(&self, x: usize, y: usize) -> bool {
        let x = x.as_i16();
        let y = y.as_i16();
        canvas::is_functional(self.version, self.version.width(), x, y)
    }

    /// Converts the QR code to a vector of booleans. Each entry represents the
    /// color of the module, with "true" means dark and "false" means light.
    pub fn to_vec(&self) -> Vec<bool> {
        self.content.iter().map(|c| *c != Color::Light).collect()
    }

    /// Returns an iterator over QR code vector of colors.
    pub fn iter(&self) -> QrCodeIterator {
        QrCodeIterator::new(&self)
    }

    /// Converts the QR code to a vector of colors.
    pub fn into_colors(self) -> Vec<Color> {
        self.content
    }
}

impl Index<(usize, usize)> for QrCode {
    type Output = Color;

    fn index(&self, (x, y): (usize, usize)) -> &Color {
        let index = y * self.width + x;
        &self.content[index]
    }
}

/// Iterate over QR code data without consuming the QR code struct
pub struct QrCodeIterator<'a> {
    qr_code: &'a QrCode,
    index: usize,
}

impl<'a> QrCodeIterator<'a> {
    fn new(qr_code: &'a QrCode) -> Self {
        let index = 0;
        QrCodeIterator { qr_code, index }
    }
}

impl<'a> Iterator for QrCodeIterator<'a> {
    type Item = bool;
    fn next(&mut self) -> Option<bool> {
        let result = self
            .qr_code
            .content
            .get(self.index)
            .map(|c| c == &Color::Dark);
        self.index += 1;
        result
    }
}

#[cfg(feature = "bmp")]
#[cfg(test)]
mod tests {
    use crate::decode::BmpDecode;

    #[test]
    fn test_rt() {
        use crate::QrCode;
        use bmp_monochrome::Bmp;
        use rand::distributions::Alphanumeric;
        use rand::Rng;
        use std::io::Cursor;

        let rand_string: String = rand::thread_rng()
            .sample_iter(&Alphanumeric)
            .take(30)
            .collect();
        let qr_code = QrCode::new(rand_string.as_bytes()).unwrap();
        let mut cursor = Cursor::new(vec![]);
        qr_code
            .to_bmp()
            .mul(3)
            .add_white_border(3)
            .write(&mut cursor)
            .unwrap();
        cursor.set_position(0);
        let bmp = Bmp::read(cursor).unwrap();
        let decoded = bmp.normalize().decode();
        assert_eq!(rand_string, decoded);
    }
}
