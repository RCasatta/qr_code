#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|qr_code_data: qr_code::QrCodeData| {
    qr_code_data.check();
});
