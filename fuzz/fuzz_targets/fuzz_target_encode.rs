#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let qr_code = qr_code::QrCode::new(data).unwrap();
    let _ = qr_code.to_bmp();
});
