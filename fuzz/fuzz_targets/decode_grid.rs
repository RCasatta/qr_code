#![no_main]

use libfuzzer_sys::fuzz_target;
use qr_code::decode::{decode, BitGrid};

struct InputGrid<'a> {
    size: usize,
    bits: &'a [u8],
}

impl BitGrid for InputGrid<'_> {
    fn size(&self) -> usize {
        self.size
    }

    fn bit(&self, y: usize, x: usize) -> bool {
        let index = y * self.size + x;
        self.bits
            .get(index / 8)
            .is_some_and(|byte| byte & (1 << (index % 8)) != 0)
    }
}

fuzz_target!(|data: &[u8]| {
    if let Some((&size, bits)) = data.split_first() {
        let grid = InputGrid {
            size: 21 + (size as usize % 40) * 4,
            bits,
        };
        let _ = decode(&grid, Vec::new());
    }
});
