format:
    aiken fmt

format-check:
    aiken fmt --check

test:
    aiken check

build:
    aiken build

ci: format-check test
