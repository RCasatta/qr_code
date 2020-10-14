#[cfg(feature = "bmp")]
fn main() {
    use qr_code::bmp_monochrome::Bmp;
    use qr_code::decode::BmpDecode;
    use std::fs::File;

    let bmp = Bmp::read(File::open("test.bmp").unwrap()).unwrap();
    println!("{}", &bmp.decode());
}

#[cfg(not(feature = "bmp"))]
fn main() {
    println!("This example needs bmp feature");
}
