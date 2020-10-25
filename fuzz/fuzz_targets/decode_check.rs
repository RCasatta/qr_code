#![no_main]
use libfuzzer_sys::fuzz_target;
use qr_code::decode::BmpDecode;

fuzz_target!(|qr_code_data: qr_code::QrCodeData| {
    let qr_code::QrCodeData { qr_code, data, mul_border } = qr_code_data;
    let bmp = match mul_border {
        None => qr_code.to_bmp(),
        Some((mul, border)) => qr_code.to_bmp().mul(mul).unwrap().add_white_border(border).unwrap().normalize(),
    };
    let decoded = bmp.decode().unwrap();
    assert_eq!(data, decoded);
});
