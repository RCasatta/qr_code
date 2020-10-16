#[cfg(feature = "bmp")]
fn main() {
    let qr_code = qr_code::QrCode::new(b"Hello").unwrap();
    let bmp = qr_code.to_bmp();
    bmp.write(std::fs::File::create("test.bmp").unwrap())
        .unwrap();
}
