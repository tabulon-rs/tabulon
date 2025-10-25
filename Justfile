
default: test

all: fmt check build test

build:
	cargo build

test:
	cargo test --workspace

fmt:
	cargo fmt --all

check:
	cargo clippy --workspace -- -D warnings
	cargo check --all

clean:
	cargo clean
