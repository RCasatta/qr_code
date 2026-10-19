# Fuzzing

The Nix development shell provides `cargo-fuzz`. Run the decoder target from
the repository root with sanitizers disabled for the stable Rust toolchain:

```sh
direnv exec . cargo fuzz run decode_grid --sanitizer none -- -max_total_time=60 -max_len=4096
```

The target starts with a known-good QR grid from `test_data/test.bmp`. It stores
new coverage inputs in `fuzz/corpus/decode_grid/`; generated inputs are ignored
by Git. Crashes are saved in `fuzz/artifacts/decode_grid/` and can be replayed
with:

```sh
direnv exec . cargo fuzz run --sanitizer none decode_grid fuzz/artifacts/decode_grid/<artifact>
```
