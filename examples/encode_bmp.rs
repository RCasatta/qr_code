use bmp_monochrome::Bmp;
use qr_code::{Color, QrCode};
use std::fs::File;

fn main() {
    let qr_code = QrCode::new(b"Hello").unwrap();
    let bmp = to_matrix(&qr_code);
    bmp.write(File::create("test.bmp").unwrap()).unwrap();
}

pub fn to_matrix(qr: &QrCode) -> Bmp {
    let width = qr.width();
    let data = qr
        .to_colors()
        .iter()
        .map(|e| match *e {
            Color::Light => false,
            Color::Dark => true,
        })
        .collect();
    Bmp::new(data, width).unwrap()
}
