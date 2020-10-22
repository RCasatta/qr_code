#[cfg(all(feature = "bmp", feature = "decode"))]
fn main() {
    use qr_code::bmp_monochrome::Bmp;
    use qr_code::decode::BmpDecode;
    use std::fs::File;

    let bmp = Bmp::read(File::open("test_data/qr_not_normalized.bmp").unwrap()).unwrap();
    println!("{}", &bmp.normalize().decode());
}
