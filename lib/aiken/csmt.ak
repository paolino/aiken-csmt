//// A Compact Sparse Merkle Trie (CSMT) — binary trie with path compression
//// and non-hashed keys, preserving key ordering.
////
//// On-chain verifier matching the Haskell CSMT implementation in haskell-mts.
//// Provides the same API surface as aiken-lang/merkle-patricia-forestry:
//// `has`, `miss`, `insert`, `delete`, `update`.
////
//// ## Differences from MPF
////
//// - Binary trie (L/R) instead of radix-16
//// - Path compression via "jumps" (Indirect type)
//// - Keys are NOT hashed — ordering is preserved
//// - Proof format: list of (consumed, sibling) steps from leaf to root

use aiken/builtin.{blake2b_256, cons_bytearray, slice_bytearray}
use aiken/csmt/bits.{key_to_bitpath}
use aiken/csmt/hashing.{
  Indirect, add_with_direction, null_hash, root_hash, serialize_key,
}
use aiken/primitive/bytearray

// -----------------------------------------------------------------------------
// ---------------------------------------------------------------- CSMT opaque
// -----------------------------------------------------------------------------

/// A Compact Sparse Merkle Trie, represented by its root hash.
pub opaque type CSMT {
  root: ByteArray,
}

// ## Constructing

/// Construct a CSMT from a known root hash. Must be 32 bytes.
pub fn from_root(root: ByteArray) -> CSMT {
  expect bytearray.length(root) == 32
  CSMT { root }
}

/// An empty CSMT.
pub const empty: CSMT = CSMT { root: null_hash }

// ## Querying

/// Check whether the trie is empty.
pub fn is_empty(self: CSMT) -> Bool {
  self.root == null_hash
}

/// Get the root hash.
pub fn root(self: CSMT) -> ByteArray {
  self.root
}

/// Test whether a key-value pair is present in the trie.
pub fn has(
  self: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> Bool {
  including(key, value, proof) == self.root
}

/// Test whether a key is absent from the trie.
pub fn miss(self: CSMT, key: ByteArray, proof: Proof) -> Bool {
  excluding(key, proof) == self.root
}

// ## Modifying

/// Insert a key-value pair. Fails if the key already exists.
pub fn insert(
  self: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> CSMT {
  expect excluding(key, proof) == self.root
  CSMT { root: including(key, value, proof) }
}

/// Delete a key-value pair. Fails if the key doesn't exist with that value.
pub fn delete(
  self: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> CSMT {
  expect including(key, value, proof) == self.root
  CSMT { root: excluding(key, proof) }
}

/// Update a key's value. Fails if the key doesn't exist with old_value.
pub fn update(
  self: CSMT,
  key: ByteArray,
  proof: Proof,
  old_value: ByteArray,
  new_value: ByteArray,
) -> CSMT {
  expect including(key, old_value, proof) == self.root
  CSMT { root: including(key, new_value, proof) }
}

// -----------------------------------------------------------------------------
// ----------------------------------------------------------------- Proof types
// -----------------------------------------------------------------------------

/// A proof for inclusion/exclusion operations.
pub type Proof {
  /// The jump path at the root node (BitPath: each byte is 0 or 1).
  root_jump: ByteArray,
  /// Steps from leaf toward root. Each step records the consumed
  /// bit count and the sibling's indirect value.
  steps: List<ProofStep>,
}

/// A single step in a proof.
pub type ProofStep {
  /// Number of key bits consumed (1 for direction + jump length).
  consumed: Int,
  /// The sibling node's indirect value (jump + hash).
  sibling: Indirect,
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------- including
// -----------------------------------------------------------------------------

/// Compute the root hash assuming the key IS present with the given value.
fn including(key: ByteArray, value: ByteArray, proof: Proof) -> ByteArray {
  let key_bits = key_to_bitpath(key)
  let leaf_hash = blake2b_256(value)
  let rj_len = bytearray.length(proof.root_jump)
  let key_after_root =
    slice_bytearray(rj_len, bytearray.length(key_bits) - rj_len, key_bits)
  let root_value =
    fold_including(
      leaf_hash,
      key_after_root,
      bytearray.length(key_after_root),
      proof.steps,
    )
  root_hash(proof.root_jump, root_value)
}

/// Walk proof steps from leaf to root, combining hashes.
/// Cursor starts at the end of key_after_root and moves toward 0.
fn fold_including(
  acc: ByteArray,
  key_ar: ByteArray,
  cursor: Int,
  steps: List<ProofStep>,
) -> ByteArray {
  when steps is {
    [] -> acc
    [ProofStep { consumed, sibling }, ..rest] -> {
      let new_cursor = cursor - consumed
      let direction = bytearray.at(key_ar, new_cursor)
      let step_jump = slice_bytearray(new_cursor + 1, consumed - 1, key_ar)
      let my_indirect = Indirect { jump: step_jump, hash: acc }
      let new_acc = add_with_direction(direction, my_indirect, sibling)
      fold_including(new_acc, key_ar, new_cursor, rest)
    }
  }
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------- excluding
// -----------------------------------------------------------------------------

/// Compute the root hash assuming the key is NOT present.
///
/// At the bottom level, the sibling absorbs the branch (its jump extends
/// with the opposite direction bit). Upper levels combine normally.
fn excluding(key: ByteArray, proof: Proof) -> ByteArray {
  let key_bits = key_to_bitpath(key)
  let rj_len = bytearray.length(proof.root_jump)
  let key_after_root =
    slice_bytearray(rj_len, bytearray.length(key_bits) - rj_len, key_bits)
  do_excluding(key_after_root, proof)
}

fn do_excluding(key_after_root: ByteArray, proof: Proof) -> ByteArray {
  when proof.steps is {
    // No steps: tree is empty without this element
    [] -> null_hash

    // At least one step: collapse the bottom branch
    [bottom_step, ..rest_steps] -> {
      let cursor = bytearray.length(key_after_root)
      let bottom_cursor = cursor - bottom_step.consumed
      let direction = bytearray.at(key_after_root, bottom_cursor)
      let opposite = 1 - direction

      // Sibling absorbs the branch: prepend opposite direction to its jump
      let collapsed =
        Indirect {
          jump: cons_bytearray(opposite, bottom_step.sibling.jump),
          hash: bottom_step.sibling.hash,
        }

      when rest_steps is {
        // Collapsed node IS the whole tree
        [] ->
          root_hash(
            bytearray.concat(proof.root_jump, collapsed.jump),
            collapsed.hash,
          )

        // Use collapsed as our indirect at the next level, then normal
        [next_step, ..upper_steps] -> {
          let next_cursor = bottom_cursor - next_step.consumed
          let next_direction = bytearray.at(key_after_root, next_cursor)
          let acc =
            add_with_direction(next_direction, collapsed, next_step.sibling)
          let root_value =
            fold_including(acc, key_after_root, next_cursor, upper_steps)
          root_hash(proof.root_jump, root_value)
        }
      }
    }
  }
}

// -----------------------------------------------------------------------------
// ----------------------------------------------------------------- Basic tests
// -----------------------------------------------------------------------------

test empty_is_empty() {
  is_empty(empty)
}

test from_root_not_empty() {
  let some_hash =
    #"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  !is_empty(from_root(some_hash))
}

// Single-element tree: insert into empty, then verify presence.
// For a single element, root_jump = full key bitpath (the root Indirect
// has jump = fullKey, hash = blake2b_256(value)).
test single_element_insert_has() {
  let key = #"01"
  let value = #"cafe"
  let key_bits = key_to_bitpath(key)
  let proof = Proof { root_jump: key_bits, steps: [] }

  let trie = insert(empty, key, value, proof)

  let expected_root = root_hash(key_bits, blake2b_256(value))
  root(trie) == expected_root
}

// Single element: insert then delete returns empty
test single_element_insert_delete() {
  let key = #"01"
  let value = #"cafe"
  let key_bits = key_to_bitpath(key)
  let proof = Proof { root_jump: key_bits, steps: [] }

  let trie = insert(empty, key, value, proof)
  let trie2 = delete(trie, key, value, proof)
  is_empty(trie2)
}

// Verify that including with empty proof produces expected hash.
// root_jump = full key bitpath for a single element.
test including_empty_proof() {
  let key = #"ab"
  let value = #"cd"
  let key_bits = key_to_bitpath(key)
  let proof = Proof { root_jump: key_bits, steps: [] }
  let result = including(key, value, proof)
  result == root_hash(key_bits, blake2b_256(value))
}

// Verify excluding with empty proof gives null_hash
test excluding_empty_proof() {
  let key = #"ab"
  let proof = Proof { root_jump: #"", steps: [] }
  excluding(key, proof) == null_hash
}

// Verify that the serialization of an empty key is correct
test serialize_empty_key() {
  serialize_key(#"") == #"0000"
}
