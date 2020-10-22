#![no_main]
use libfuzzer_sys::fuzz_target;
use qr_code::decode::BmpDecode;

fuzz_target!(|qr: qr_code::QrCode| {
    let _ = qr.to_bmp().decode().unwrap();
});
