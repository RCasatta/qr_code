export JOBS=${JOBS:=1}
cargo +nightly fuzz run fuzz_target_rt -- -jobs=$JOBS -max_len=2000 # max byte size encodable with qr code V40-M