format:
    aiken fmt

format-check:
    aiken fmt --check

generate-vectors:
    #!/usr/bin/env bash
    set -euo pipefail
    nix build .#test-vectors --quiet
    work=$(mktemp -d)
    trap 'rm -rf "$work"' EXIT
    # One module per marker; csplit fails when a marker is missing.
    csplit -z -f "$work/part-" result \
        '/^\/\/ FIFO test vectors/' \
        '/^\/\/ Random-tree test vectors/' \
        '/^\/\/ Measurement test vectors/' >/dev/null
    cp -f "$work/part-00" lib/aiken/csmt/vectors.ak
    {
        echo "// Auto-generated FIFO test vectors from haskell-mts"
        echo ""
        echo "use aiken/csmt.{Proof, ProofStep, empty, from_root}"
        echo "use aiken/csmt/fifo.{Fifo, is_empty, pop, push, root_hash}"
        echo "use aiken/csmt/hashing.{Indirect}"
        echo ""
        # Strip comment header and use lines from the generated section
        sed '/^\/\/ FIFO/d; /^use /d; /^$/d; 1s/^/\n/' "$work/part-01"
    } > lib/aiken/csmt/fifo_vectors.ak
    cp -f "$work/part-02" lib/aiken/csmt/random_vectors.ak
    cp -f "$work/part-03" lib/aiken/csmt/measure_vectors.ak
    aiken fmt

# Property tests run with a fixed seed and case count: a pass is repeatable, and
# relaxation-check promises that every planted relaxation fails a test at exactly these values.
seed := "61"
cases := "200"

test:
    aiken check --seed {{seed}} --max-success {{cases}}

relaxation-check:
    scripts/relaxation-check {{seed}} {{cases}}

build:
    aiken build

vector-modules := "lib/aiken/csmt/vectors.ak lib/aiken/csmt/fifo_vectors.ak lib/aiken/csmt/random_vectors.ak lib/aiken/csmt/measure_vectors.ak"

# Every vector module must be committed and equal to its regenerated text. `git diff` alone
# says nothing about a module that was never committed.
vectors-check:
    #!/usr/bin/env bash
    set -euo pipefail
    just generate-vectors
    for f in {{vector-modules}}; do
        if ! git cat-file -e "HEAD:$f" 2>/dev/null; then
            echo "ERROR: $f is not committed — run 'just generate-vectors' and commit"
            exit 1
        fi
    done
    if ! git diff --exit-code HEAD -- {{vector-modules}}; then
        echo "ERROR: committed vectors are stale — run 'just generate-vectors' and commit"
        exit 1
    fi

ci: vectors-check format-check test relaxation-check
