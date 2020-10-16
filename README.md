qr_code
=======

[![crates.io](https://img.shields.io/crates/v/qr_code.svg)](https://crates.io/crates/qr_code)
[![MIT OR Apache 2.0](https://img.shields.io/badge/license-MIT%20%2f%20Apache%202.0-blue.svg)](./LICENSE-APACHE.txt)

QR code and Micro QR code encoder in Rust. [Documentation](https://docs.rs/qr_code).

This lib forked https://docs.rs/qrcode mainly because of lack of support to structured QR code (multiple QR codes)
even if the minimal change required has been pushed https://github.com/kennytm/qrcode-rust/pull/44

Moreover dependencies `image`, `checked_int_cast` and module `render` has been removed with a view to simplicity.

Example
-------

## Bmp image  generation

requires `bmp` feature

```rust
let qr_code = qr_code::QrCode::new(b"Hello").unwrap();
let bmp = qr_code.to_bmp();
bmp.write(std::fs::File::create("test.bmp").unwrap()).unwrap();
```

Generate this image:

![test](https://raw.githubusercontent.com/RCasatta/qr_code/master/test.bmp)

Looks small?

Many context supports rescaling mode specific for pixelated images, for example in html `image-rendering: pixelated;`

As an alternative see method `Bmp::mul` and `Bmp::add_whitespace`

## Unicode string generation

```rust
let qr_code = qr_code::QrCode::new(b"Hello").unwrap();
println!("{}", qr_code.to_string(false));
```

Generates this output (looks better in terminal):

```text

   █▀▀▀▀▀█  ▀▀▀█ █▀▀▀▀▀█
   █ ███ █ █ █ ▀ █ ███ █
   █ ▀▀▀ █ ██ ▄▀ █ ▀▀▀ █
   ▀▀▀▀▀▀▀ █ █ ▀ ▀▀▀▀▀▀▀
   ▀ ▀█▀▀▀ ▄▀ █▄▄█▀▀██ ▄
     █▀▀█▀▄▄▀█▄█▄█▀ ██▀ 
    ▀▀▀  ▀▀█▀▀ █  █ ▄  ▀
   █▀▀▀▀▀█ ▄▀▄▀ ▀ ▄█▄██ 
   █ ███ █ █▄ █▄█▄▄▀▄ ▀ 
   █ ▀▀▀ █ ▀█ ▄█▄█▀▄▄█  
   ▀▀▀▀▀▀▀ ▀▀  ▀   ▀  ▀ 

```
