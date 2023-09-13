fn main() {
    let args: Vec<String> = std::env::args().collect();
    let default = "Hello".to_string();
    let data = args.get(1).unwrap_or(&default);
    let qr_code = qr_code::QrCode::new(data.as_bytes()).unwrap();
    println!("{}", qr_code.to_string(true, 3));
}
