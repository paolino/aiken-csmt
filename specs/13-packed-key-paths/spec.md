# Spec: packed key paths (issue #13)

## User story

As a contract author who verifies CSMT proofs on-chain, I want `has`, `miss` and `insert` to cost a small fraction
of a transaction at 1 000 and 100 000 keys, without giving up any of the soundness shown in #10 and in
lambdasistemi/haskell-mts#172.

## Facts

- Cost at v0.1.0 (#11 table, aiken v1.1.21, haskell-mts vectors, 32-byte keys): `insert` at 1 000 keys 12 485 409 mem
  / 3.69 G cpu (89% of a 14 M memory limit); `has` 7.0 M mem; `miss` 5.5 M mem. Reference: guarded
  merkle-patricia-forestry inserts into about 845 000 keys at 0.39 M mem / 0.11 G cpu.
- The verifier expands the key to one byte per bit (`key_to_bitpath`, 8 `cons_bytearray` per key byte), slices it at
  every step, and packs every jump back to bytes for hashing (`pack_bits`, one recursion per bit, with the bit check).
- The hashed serialization is already packed: `putKey` = 2-byte bit count + bits packed MSB-first, zero-padded. Roots
  therefore do not depend on the proof's in-memory representation: a verifier and a proof format that work on packed
  bits can produce byte-identical roots, so existing trees stay valid.
- Plutus V3 bitwise builtins are available to this project (`shift_bytearray`, `read_bit`, `and_bytearray`, … checked
  with the dev-shell aiken).

## Requirements

| name | statement |
|---|---|
| roots-unchanged | for every tree, the root is byte-identical before and after (haskell-mts vectors, all four modules) |
| cost-target | `has`, `miss` and `insert` at 1 000 and 100 000 keys of 32 bytes each cost at most 1.0 M memory units and 0.3 G cpu (about 2.5 times guarded MPF); the measured table is reported either way and decides the next step, not acceptance of a slice |
| soundness-kept | every soundness property of #10 holds on the new representation and format, with each field's whole domain covered again |
| new-domains-covered | packed fields add domains — bit count against byte length, non-zero padding bits, byte lengths not equal to ceil(bits/8), counts past the key — each generated, each refused or shown harmless, each with a planted relaxation killed in CI |
| completeness-kept | every honest haskell-mts proof (random-tree vectors) is accepted |
| format-agreement | aiken-csmt and haskell-mts never disagree on a released proof format: a format change ships as a versioned pair (aiken-csmt release + haskell-mts release whose Plutus-data encoder and vectors emit it) |
| measured | the #11 method gives a before/after table at 1, 10, 1 000, 100 000 keys in the PR body |

## Non-goals

Changing the hash format (leaf/branch domain separation is #12), Singular, MPF.
