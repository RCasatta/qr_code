use crate::{Color, QrCode};

impl QrCode {
    pub fn to_string(&self, inverted: bool) -> String {
        let mut result = String::new();
        let width = self.width();
        let mut qr_code = self.clone().into_colors();
        let height = qr_code.len() / width;
        qr_code.extend(vec![Color::Light; width]);

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
                let val = match (
                    qr_code[start],
                    qr_code.get(start + width).unwrap_or(&Color::Light),
                ) {
                    (Color::Light, Color::Light) => 0,
                    (Color::Light, Color::Dark) => 1,
                    (Color::Dark, Color::Light) => 2,
                    (Color::Dark, Color::Dark) => 3,
                };
                result.push_str(&blocks[val + inverted].to_string());
            }
            result.push_str("\n");
        }
        result.push_str("\n");
        result
    }

    #[cfg(feature = "bmp")]
    pub fn to_bmp(self) -> bmp_monochrome::Bmp {
        let width = self.width();
        let data = self
            .to_colors()
            .iter()
            .map(|e| match *e {
                Color::Light => false,
                Color::Dark => true,
            })
            .collect();
        bmp_monochrome::Bmp::new(data, width).unwrap()
    }
}
