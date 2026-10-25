//// A Compact Sparse Merkle Trie (CSMT) — binary trie with path compression
//// and non-hashed keys, preserving key ordering.
////
//// On-chain verifier matching the Haskell CSMT implementation in haskell-mts.
//// Provides the same API surface as aiken-lang/merkle-patricia-forestry:
//// `has`, `miss`, `insert`, `delete`, `update`, `pop`, `pop_max`,
//// `push_min`, `push_max`.
////
//// ## Differences from MPF
////
//// - Binary trie (L/R) instead of radix-16
//// - Path compression via "jumps" (Indirect type)
//// - Keys are NOT hashed — ordering is preserved
//// - Proof format: list of (consumed, sibling) steps from leaf to root
////
//// ## Key length
////
//// Every tree must hold keys of one fixed length, and `has`, `delete`,
//// `update`, `pop` and `pop_max` decide membership only for keys of that
//// length. The node hash does not tell a leaf from a branch, so the root alone
//// does not fix the depth of a leaf: a key shorter than the tree's keys can
//// verify with a value that is the serialized pair of an internal node's
//// children. A caller whose keys are digests of one fixed length satisfies the
//// obligation; any other caller must check the key length itself.

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
pub fn has(self: CSMT, key: ByteArray, value: ByteArray, proof: Proof) -> Bool {
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

/// Remove the minimum element from the trie. Verifies that the
/// key-value pair exists AND that it is the smallest key (every
/// branch decision goes left). Returns the trie without the element.
///
/// #### Fails when
///
/// - The proof is invalid.
/// - The element doesn't exist with that value.
/// - The key is not the minimum (some branch goes right).
pub fn pop(self: CSMT, key: ByteArray, value: ByteArray, proof: Proof) -> CSMT {
  expect including_minimum(key, value, proof) == self.root
  CSMT { root: excluding(key, proof) }
}

/// Remove the maximum element from the trie. Verifies that the
/// key-value pair exists AND that it is the largest key (every
/// branch decision goes right). Returns the trie without the element.
///
/// #### Fails when
///
/// - The proof is invalid.
/// - The element doesn't exist with that value.
/// - The key is not the maximum (some branch goes left).
pub fn pop_max(
  self: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> CSMT {
  expect including_maximum(key, value, proof) == self.root
  CSMT { root: excluding(key, proof) }
}

/// Insert the minimum element into the trie. Verifies that the
/// key is absent AND that it would be the smallest key (every
/// branch decision goes left). Returns the trie with the element.
///
/// #### Fails when
///
/// - The proof is invalid.
/// - The key already exists.
/// - The key is not the minimum (some branch goes right).
pub fn push_min(
  self: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> CSMT {
  expect excluding_minimum(key, proof) == self.root
  CSMT { root: including(key, value, proof) }
}

/// Insert the maximum element into the trie. Verifies that the
/// key is absent AND that it would be the largest key (every
/// branch decision goes right). Returns the trie with the element.
///
/// #### Fails when
///
/// - The proof is invalid.
/// - The key already exists.
/// - The key is not the maximum (some branch goes left).
pub fn push_max(
  self: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> CSMT {
  expect excluding_maximum(key, proof) == self.root
  CSMT { root: including(key, value, proof) }
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

/// The bits of the key below the root jump. The root jump is hashed as given,
/// so it must be exactly the leading bits of the key: any other jump would
/// let the proof of one key stand for another.
fn after_root_jump(key_bits: ByteArray, root_jump: ByteArray) -> ByteArray {
  let rj_len = bytearray.length(root_jump)
  expect slice_bytearray(0, rj_len, key_bits) == root_jump
  slice_bytearray(rj_len, bytearray.length(key_bits) - rj_len, key_bits)
}

/// Compute the root hash assuming the key IS present with the given value.
fn including(key: ByteArray, value: ByteArray, proof: Proof) -> ByteArray {
  let key_after_root = after_root_jump(key_to_bitpath(key), proof.root_jump)
  let leaf_hash = blake2b_256(value)
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
/// Cursor starts at the end of key_after_root and moves toward 0, where the
/// steps must end: key bits left over would be unhashed.
fn fold_including(
  acc: ByteArray,
  key_ar: ByteArray,
  cursor: Int,
  steps: List<ProofStep>,
) -> ByteArray {
  when steps is {
    [] -> {
      expect cursor == 0
      acc
    }
    [ProofStep { consumed, sibling }, ..rest] -> {
      expect consumed >= 1
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
// ------------------------------------------------------- including + extremum
// -----------------------------------------------------------------------------

/// Like `including`, but also asserts the key is the minimum: every
/// branch direction must be 0 (left).
fn including_minimum(
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> ByteArray {
  including_extremum(0, key, value, proof)
}

/// Like `including`, but also asserts the key is the maximum: every
/// branch direction must be 1 (right).
fn including_maximum(
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> ByteArray {
  including_extremum(1, key, value, proof)
}

/// Like `including`, but asserts every branch direction equals `expected_dir`.
fn including_extremum(
  expected_dir: Int,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> ByteArray {
  let key_after_root = after_root_jump(key_to_bitpath(key), proof.root_jump)
  let leaf_hash = blake2b_256(value)
  let root_value =
    fold_including_extremum(
      expected_dir,
      leaf_hash,
      key_after_root,
      bytearray.length(key_after_root),
      proof.steps,
    )
  root_hash(proof.root_jump, root_value)
}

/// Same as fold_including but expects direction == expected_dir at every step.
fn fold_including_extremum(
  expected_dir: Int,
  acc: ByteArray,
  key_ar: ByteArray,
  cursor: Int,
  steps: List<ProofStep>,
) -> ByteArray {
  when steps is {
    [] -> {
      expect cursor == 0
      acc
    }
    [ProofStep { consumed, sibling }, ..rest] -> {
      expect consumed >= 1
      let new_cursor = cursor - consumed
      let direction = bytearray.at(key_ar, new_cursor)
      expect direction == expected_dir
      let step_jump = slice_bytearray(new_cursor + 1, consumed - 1, key_ar)
      let my_indirect = Indirect { jump: step_jump, hash: acc }
      let new_acc = add_with_direction(direction, my_indirect, sibling)
      fold_including_extremum(expected_dir, new_acc, key_ar, new_cursor, rest)
    }
  }
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------- excluding
// -----------------------------------------------------------------------------

/// Compute the root hash assuming the key is NOT present.
fn excluding(key: ByteArray, proof: Proof) -> ByteArray {
  do_excluding(None, key, proof)
}

/// Remove the key from the path the proof describes and hash what is left.
///
/// The proof is the one the key has in the tree that holds it: its lowest step
/// is the branch the key hangs from, whose other child, the sibling, takes the
/// branch's place. That child keeps the key bits between the branch above (the
/// start of the key below the root jump, when there is none) and the removed
/// branch, then the bit the key did not take, then its own jump, so that no key
/// bit goes unhashed. The steps above the lowest consume at least one bit each
/// and end at the start of the key, as the including folds require. A lowest
/// step that points outside the key is refused by the index read, and a root
/// jump is hashed as given: one that is not the key's can only reproduce the
/// root of a tree that does not hold the key.
///
/// With an `expected_dir`, every branch the key sits at must go that way.
fn do_excluding(
  expected_dir: Option<Int>,
  key: ByteArray,
  proof: Proof,
) -> ByteArray {
  let key_bits = key_to_bitpath(key)
  let rj_len = bytearray.length(proof.root_jump)
  let key_after_root =
    slice_bytearray(rj_len, bytearray.length(key_bits) - rj_len, key_bits)
  when proof.steps is {
    // No steps: tree is empty without this element
    [] -> null_hash

    // At least one step: collapse the bottom branch
    [bottom_step, ..rest_steps] -> {
      let bottom_cursor =
        bytearray.length(key_after_root) - bottom_step.consumed
      let direction = bytearray.at(key_after_root, bottom_cursor)
      expect goes(expected_dir, direction)

      when rest_steps is {
        // Collapsed node IS the whole tree
        [] -> {
          let collapsed =
            collapse(key_after_root, 0, bottom_cursor, direction, bottom_step)
          root_hash(
            bytearray.concat(proof.root_jump, collapsed.jump),
            collapsed.hash,
          )
        }

        // Use collapsed as our indirect at the next level, then normal
        [next_step, ..upper_steps] -> {
          expect next_step.consumed >= 1
          let next_cursor = bottom_cursor - next_step.consumed
          let next_direction = bytearray.at(key_after_root, next_cursor)
          expect goes(expected_dir, next_direction)
          let collapsed =
            collapse(
              key_after_root,
              next_cursor + 1,
              bottom_cursor,
              direction,
              bottom_step,
            )
          let acc =
            add_with_direction(next_direction, collapsed, next_step.sibling)
          let root_value =
            when expected_dir is {
              None ->
                fold_including(acc, key_after_root, next_cursor, upper_steps)
              Some(dir) ->
                fold_including_extremum(
                  dir,
                  acc,
                  key_after_root,
                  next_cursor,
                  upper_steps,
                )
            }
          root_hash(proof.root_jump, root_value)
        }
      }
    }
  }
}

/// The sibling of the removed branch in the branch's place: the key bits from
/// `above` (just after the branch bit above) to the removed branch bit, the
/// bit the key did not take, and the sibling's own jump.
fn collapse(
  key_after_root: ByteArray,
  above: Int,
  bottom_cursor: Int,
  direction: Int,
  bottom_step: ProofStep,
) -> Indirect {
  Indirect {
    jump: bytearray.concat(
      slice_bytearray(above, bottom_cursor - above, key_after_root),
      cons_bytearray(1 - direction, bottom_step.sibling.jump),
    ),
    hash: bottom_step.sibling.hash,
  }
}

/// Whether a branch bit is the one an extremum requires, if one is required.
fn goes(expected_dir: Option<Int>, direction: Int) -> Bool {
  when expected_dir is {
    None -> True
    Some(dir) -> direction == dir
  }
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------- excluding + extremum
// -----------------------------------------------------------------------------

/// Like `excluding`, but asserts the key is the minimum: every
/// branch direction must be 0 (left).
fn excluding_minimum(key: ByteArray, proof: Proof) -> ByteArray {
  do_excluding(Some(0), key, proof)
}

/// Like `excluding`, but asserts the key is the maximum: every
/// branch direction must be 1 (right).
fn excluding_maximum(key: ByteArray, proof: Proof) -> ByteArray {
  do_excluding(Some(1), key, proof)
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
