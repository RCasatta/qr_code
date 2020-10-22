#![no_main]
use libfuzzer_sys::fuzz_target;
use qr_code::decode::BmpDecode;

fuzz_target!(|qr_code_data: qr_code::QrCodeData| {
    let qr_code::QrCodeData { qr_code, data } = qr_code_data;
    let decoded = qr_code.to_bmp().decode().unwrap();
    assert_eq!(data, decoded);
});
