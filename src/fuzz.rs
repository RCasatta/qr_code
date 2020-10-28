use crate::{QrCode, Version};

impl arbitrary::Arbitrary for QrCode {
    fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
        let level = crate::EcLevel::arbitrary(u)?;
        let version = crate::Version::arbitrary(u)?;
        let data = <Vec<u8>>::arbitrary(u)?;
        let qr_code = QrCode::with_version(data, version, level)
            .map_err(|_| arbitrary::Error::IncorrectFormat)?;
        Ok(qr_code)
    }
}

#[derive(Debug)]
/// doc
pub struct QrCodeData {
    /// qr
    pub qr_code: QrCode,
    /// data
    pub data: Vec<u8>,
    /// mul
    pub mul_border: Option<(u8, u8)>,
}

impl arbitrary::Arbitrary for QrCodeData {
    fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
        let level = crate::EcLevel::arbitrary(u)?;
        let version = crate::Version::arbitrary(u)?;
        let data = <Vec<u8>>::arbitrary(u)?;
        let qr_code = QrCode::with_version(&data, version, level)
            .map_err(|_| arbitrary::Error::IncorrectFormat)?;
        let mul_border = u8::arbitrary(u)?;
        let mul_border = if mul_border % 2 == 0 {
            None
        } else {
            Some(((mul_border / 64) + 2, (mul_border % 64) + 1))
        };

        Ok(QrCodeData {
            qr_code,
            data,
            mul_border,
        })
    }
}

impl arbitrary::Arbitrary for Version {
    fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
        let v = u8::arbitrary(u)?;
        match v {
            1..=40 => Ok(Version::Normal(v as i16)),
            //41..=44 => Ok(Version::Micro((v-40u8) as i16)),  not supported for now
            _ => Err(arbitrary::Error::IncorrectFormat),
        }
    }
}

#[cfg(test)]
mod tests {
    /*
    #[test]
    fn test_fuzz_base() {
        let data = base64::decode("0///yigN//8RB///Ef9AFwcu/8ooDf//").unwrap();
        let unstructured = arbitrary::Unstructured::new(&data[..]);
        let data = QrCodeData::arbitrary_take_rest(unstructured).unwrap();
        dbg!(data);
    }
    */

    /*
    #[test]
    fn test_fuzz() {
        use crate::decode::BmpDecode;
        let data = include_bytes!("../test_data/crash-70ecec40327a1b122e0c3346e383de8154e66b73");
        let code = crate::QrCode::new(data).unwrap();
        let result = code.to_bmp().mul(2).add_white_border(2).normalize().decode().unwrap();
        assert_eq!(result, data);
    }
    */
}
