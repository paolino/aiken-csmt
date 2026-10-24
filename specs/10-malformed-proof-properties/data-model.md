# Data model

Unchanged types: `Proof { root_jump, steps }`, `ProofStep { consumed, sibling }`,
`Indirect { jump, hash }`.

Validity of a proof for key `K` (bit path `B`, length `n`), as enforced after
this ticket — each line is accepted only if the generator shows it is needed:

- `root_jump` is a prefix of `B`.
- Every jump byte (root and sibling) is 0 or 1.
- Every `consumed` is at least 1.
- The steps' `consumed` values sum exactly to `n - length(root_jump)`, so the
  walk ends at the root's branch bit and no key bit is left unhashed.
- Every sibling hash is 32 bytes.

Generator domain per field: bytes 0..255 at every jump position; jump lengths
0..(n + slack); `consumed` over negative, zero, 1..n, past n; hashes of length
0, 31, 32, 33 and random content plus honest hashes; step lists from empty to
longer than the key.
