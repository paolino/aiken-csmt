# Plan: issue #13

Class: changes behaviour (on-chain verifier; proof format in the second phase). Topology: OWNER per slice, commit owner
Claude Sonnet 5.5 xhigh, auditor Muse (operator staffing kept by the epic owner, 2026-10-25).

## Strategy: measure first, change the format only if the internals are not enough

1. Packed internals with the proof format unchanged: the key stays packed (never expanded); key-derived jumps are cut
   from the packed key with shifts and masks; the serialization of a key-derived jump is built directly; proof-supplied
   jumps (byte per bit) are packed once at the boundary. Roots and proofs unchanged, so every test of v0.1.0 passes as
   is. Measure.
2. If the target is not met, change the proof format so proof-supplied jumps arrive packed (bit count + packed bytes,
   the `putKey` shape), removing the boundary packing: a versioned format released as a pair with haskell-mts (Plutus
   data encoder, vector emitter, Haskell/TypeScript decoders). Roots still unchanged.

## Slices (each under two hours)

| slice | repository | content | depends on |
|---|---|---|---|
| packed-primitives | aiken-csmt | packed bit-path functions (cut a bit range, concatenate bit strings, read a bit, serialize a packed path) with properties equating them to the byte-per-bit reference over all lengths and offsets | none |
| packed-verifier | aiken-csmt | `including`/`excluding` and the extremum variants on packed keys; proof format unchanged; all v0.1.0 tests, vectors, relaxations pass; new relaxations for any new check; cost table | packed-primitives |
| decide | ticket owner | from the table: target met, release 0.2.0; else journal the table and wait for the epic owner (operator decision) before the format change | packed-verifier |
| packed-format-haskell | haskell-mts | proof format v2 (packed jumps) in the Plutus-data encoding and the Aiken vector emitter, alongside v1 until the pair ships; Haskell and TypeScript decoders refuse non-canonical packed fields | decide |
| packed-format-aiken | aiken-csmt | `Proof`/`ProofStep` v2; malformed-proof generators over the new domains; relaxations; pin bump; cost table; release 0.2.0 paired with the haskell-mts release | packed-format-haskell merged |

## Gate (from ci.yml / CI.yaml)

aiken-csmt: `nix develop --quiet -c just ci` (vectors-check, format-check, test at seed 61 / 200 cases,
relaxation-check). haskell-mts: the rows of its CI.yaml (build, unit-tests, typescript tests, format-check, hlint,
cabal check). Every command in `systemd-run --user --scope --unit=csmt-<what>-<n> -p MemoryMax=16G timeout 3600 ...`.

## Open questions for plan review

1. Cost target: 20% of each limit per operation at 1 000 and 100 000 keys (recommended), or a ratio to guarded MPF?
2. If the decide step stops after packed-verifier, is a 0.2.0 release with an unchanged proof format acceptable
   (recommended: yes, it is a pure cost release)?
