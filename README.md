qr_code
=======

[![crates.io](https://img.shields.io/crates/v/qrcode.svg)](https://crates.io/crates/qr_code)
[![MIT OR Apache 2.0](https://img.shields.io/badge/license-MIT%20%2f%20Apache%202.0-blue.svg)](./LICENSE-APACHE.txt)

QR code and Micro QR code encoder in Rust. [Documentation](https://docs.rs/qr_code).

Example
-------

## Bmp image  generation

// TODO

## Unicode string generation

```rust
use qr_code::QrCode;
use qr_code::render::unicode;

fn main() {
    let code = QrCode::new("mow mow").unwrap();
    let image = code.render::<unicode::Dense1x2>()
        .dark_color(unicode::Dense1x2::Light)
        .light_color(unicode::Dense1x2::Dark)
        .build();
    println!("{}", image);
}
```

Generates this output:

```text
█████████████████████████████
█████████████████████████████
████ ▄▄▄▄▄ █ ▀▀▀▄█ ▄▄▄▄▄ ████
████ █   █ █▀ ▀ ▀█ █   █ ████
████ █▄▄▄█ ██▄  ▀█ █▄▄▄█ ████
████▄▄▄▄▄▄▄█ ▀▄▀ █▄▄▄▄▄▄▄████
████▄▀ ▄▀ ▄ █▄█  ▀ ▀█ █▄ ████
████▄██▄▄▀▄▄▀█▄ ██▀▀█▀▄▄▄████
█████▄▄▄█▄▄█  ▀▀▄█▀▀▀▄█▄▄████
████ ▄▄▄▄▄ █   ▄▄██▄ ▄ ▀▀████
████ █   █ █▀▄▄▀▄▄ ▄▄▄▄ ▄████
████ █▄▄▄█ █▄  █▄▀▄▀██▄█▀████
████▄▄▄▄▄▄▄█▄████▄█▄██▄██████
█████████████████████████████
▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀
```
