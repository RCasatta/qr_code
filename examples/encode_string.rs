use qr_code::types::Color::{Dark, Light};
use qr_code::QrCode;

fn main() {
    let qr_code = QrCode::new(b"Hello").unwrap();
    let inverted = false;
    let mut result = String::new();
    let width = qr_code.width();
    let mut qr_code = qr_code.clone().into_colors();
    let height = qr_code.len() / width;
    qr_code.extend(vec![Light; width]);

    let inverted = if inverted { 0 } else { 4 };
    let blocks = ["█", "▀", "▄", " ", " ", "▄", "▀", "█"];
    result.push_str("\n\n");
    for i in (0..height).step_by(2) {
        result.push_str(&format!(
            "{}{}{}",
            blocks[inverted], blocks[inverted], blocks[inverted]
        ));
        for j in 0..width {
            let start = i * width + j;
            let val = match (qr_code[start], qr_code.get(start + width).unwrap_or(&Light)) {
                (Light, Light) => 0,
                (Light, Dark) => 1,
                (Dark, Light) => 2,
                (Dark, Dark) => 3,
            };
            result.push_str(&blocks[val + inverted].to_string());
        }
        result.push_str("\n");
    }
    result.push_str("\n");
    println!("{}", result);
}
