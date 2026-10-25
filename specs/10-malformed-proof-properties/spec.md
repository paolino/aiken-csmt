# Spec: generated malformed-proof properties (issue #10)

## User story

As a contract author who uses `miss` to enforce "this key is new" and `has` to
enforce "this key holds this value", I want no proof, however malformed, to
make a false statement verify, while every honest proof built by haskell-mts
is still accepted.

## Finding on main (a711011)

A probe against the verifier at a711011 (not committed) shows both directions
broken on a one-key tree:

- `has(T, #"02", v, P)` is true where `T` holds only `#"01" -> v` and `P` is
  the honest proof of `#"01"`: `root_jump` is hashed but never compared with
  the key's bits.
- `miss(T, #"0f", P)` is true where `T` holds only `#"0f"`: a bottom step whose
  `consumed` is shorter than the remaining key path leaves key bits unhashed,
  so the collapsed neighbour can be the key's own leaf.

`insert`, `delete`, `update`, `pop`, `pop_max`, `push_min` and `push_max` share
these folds and inherit both defects.

## Requirements

Soundness holds for every proof, with every field drawn from its whole domain:
`root_jump` and sibling jump bytes of any value 0..255 and any length,
`consumed` of any integer (zero, negative, past the key length), sibling
hashes of any length and content, step lists of any length.

| name | statement |
|---|---|
| miss-rejects-held-key | for a tree holding `K`, `miss(T, K, P)` is false or fails for every `P` |
| insert-rejects-held-key | for a tree holding `K`, `insert(T, K, v, P)` fails for every `P` and `v` |
| push-rejects-held-key | same for `push_min` and `push_max` |
| has-rejects-wrong-value | for a tree holding `K -> v`, `has(T, K, w, P)` is false or fails for every `P` and every `w != v` |
| has-rejects-absent-key | for a tree whose keys all have length `L` and a key `K` of length `L` it does not hold, `has(T, K, w, P)` is false or fails for every `P`, `w` |
| has-rejects-other-length-key | for a key whose length differs from `L`, `has(T, K, w, P)` is false or fails for every `P` and every `w` that is not a branch preimage of `T` |
| removal-rejects-false-membership | `delete`, `update`, `pop`, `pop_max` fail whenever the matching `has` statement is false |
| honest-proofs-accepted | for random trees built by haskell-mts, every member's inclusion proof makes `has` true, every absent key's proof makes `miss` true, and `insert` with it yields the haskell-mts root after insertion |
| range-check-kills-relaxation | each range check added by this ticket, if removed or relaxed, makes at least one soundness property fail; this runs in CI |
| failing-case-kept | each counterexample the generator found is kept as a named unit test |
| case-count-recorded | CI runs the properties with a fixed `--max-success`, and the PR records the number |

Trees in the properties hold keys of one length (the haskell-mts model). The
queried keys of `has-rejects-other-length-key` include prefixes and extensions
of held keys.

Leaf and branch hashes are not domain-separated: a value equal to
`ser(left) ++ ser(right)` hashes like the branch with those children, so a key
ending at that branch (a prefix of held keys) verifies with that value. No
proof check can exclude it, because the verifier does not know the tree's key
length. The library therefore requires every tree to hold keys of one fixed
length (documented in `lib/aiken/csmt.ak`); a caller that hashes its keys meets
it. Changing the hash format is out of scope.

Rejection means the function returns false or the script fails; both are
acceptable on-chain. The proof format (`Proof`, `ProofStep`, `Indirect`) does
not change.

## Measurement

Proof size (bytes of the serialized `Proof` data) and verification cost (mem,
cpu) for inclusion, exclusion and insert, at trees of 1, 10, 1 000 and 100 000
keys, before and after the range checks. Published in the PR body.

## Release

A version Singular can pin: `aiken.toml` version and a tag on the merged head.

## Non-goals

Singular, aiken-lang/merkle-patricia-forestry, issues #5 and #8, proof
uniqueness beyond soundness (two accepted proofs for one true statement are
not a defect), the FIFO module beyond the shared verifier.
