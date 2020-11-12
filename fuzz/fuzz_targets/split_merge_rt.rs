#![no_main]
use libfuzzer_sys::fuzz_target;
use qr_code::split_merge_rt;

fuzz_target!(|data: (i16, Vec<u8>)| {
    let (version, bytes) = data;
    split_merge_rt(version, bytes);
});
