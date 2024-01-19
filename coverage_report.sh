#!/bin/sh
cargo clean && rm *.profraw
RUSTFLAGS="-C instrument-coverage" cargo test
rust-profdata merge -sparse *.profraw -o tests_coverage.profdata
rust-cov report --use-color --ignore-filename-regex='/.cargo/registry' --ignore-filename-regex='/src/tests/'  --ignore-filename-regex='/library/std/src/' --instr-profile=tests_coverage.profdata --object ../target/debug/deps/bva-*
