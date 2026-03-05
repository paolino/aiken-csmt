format:
    aiken fmt

format-check:
    aiken fmt --check

generate-vectors:
    #!/usr/bin/env bash
    set -euo pipefail
    nix build .#test-vectors --quiet
    csplit -z -f /tmp/csmt-vec- result '/^\/\/ FIFO test vectors/' '{*}' >/dev/null
    cp -f /tmp/csmt-vec-00 lib/aiken/csmt/vectors.ak
    if [ -f /tmp/csmt-vec-01 ] && [ -f lib/aiken/csmt/fifo.ak ]; then
        {
            echo "// Auto-generated FIFO test vectors from haskell-mts"
            echo ""
            echo "use aiken/csmt.{Proof, ProofStep, empty, from_root}"
            echo "use aiken/csmt/fifo.{Fifo, is_empty, pop, push, root_hash}"
            echo "use aiken/csmt/hashing.{Indirect}"
            echo ""
            # Strip comment header and use lines from the generated section
            sed '/^\/\/ FIFO/d; /^use /d; /^$/d; 1s/^/\n/' /tmp/csmt-vec-01
        } > lib/aiken/csmt/fifo_vectors.ak
    fi
    rm -f /tmp/csmt-vec-*
    aiken fmt

test:
    aiken check

build:
    aiken build

ci: generate-vectors format-check test
