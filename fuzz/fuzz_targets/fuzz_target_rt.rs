#![no_main]
use libfuzzer_sys::fuzz_target;
use qr_code::decode::BmpDecode;

fuzz_target!(|data: &[u8]| {
    let result = qr_code::QrCode::new(data).unwrap().to_bmp().mul(2).add_white_border(2).normalize().decode().unwrap();
    assert_eq!(result, data);
});
