# Modules model

| module | responsibility | change |
|---|---|---|
| `lib/aiken/csmt.ak` | verifier: `including`, `excluding` and their extremum variants | adds range checks; no change to public types or signatures |
| `lib/aiken/csmt/hashing.ak`, `bits.ak` | serialization and bit paths | unchanged unless a range check belongs at serialization (owner's choice, recorded) |
| property module(s) under `lib/aiken/csmt/` (test-only) | soundness generators and properties; failing cases kept | new |
| `lib/aiken/csmt/vectors.ak` | generated from haskell-mts | regenerated when the haskell-mts pin moves |
| relaxation mutants and runner (test tooling) | apply each planted relaxation, require the suite to fail | new; wired into `just ci` |
| `justfile`, `flake.nix` | gate commands, haskell-mts pin | `test` fixes `--max-success`; `ci` runs the relaxation check |

Dependency direction: tests depend on the verifier and the vectors; the
verifier depends on nothing new.
