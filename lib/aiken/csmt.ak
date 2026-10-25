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

use aiken/builtin.{blake2b_256}
use aiken/csmt/bits.{
  key_to_bitpath, packed_bit, packed_concat, packed_from_bitpath, packed_single,
  packed_slice,
}
use aiken/csmt/hashing.{
  Indirect, branch_hash, null_hash, root_hash, serialize_cut_head, serialize_key,
  serialize_packed_indirect, serialize_sibling, unjumped_head,
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
  let (without, with) = without_and_with(None, key, value, proof)
  expect without == self.root
  CSMT { root: with }
}

/// Delete a key-value pair. Fails if the key doesn't exist with that value.
pub fn delete(
  self: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> CSMT {
  let (without, with) = without_and_with(None, key, value, proof)
  expect with == self.root
  CSMT { root: without }
}

/// Update a key's value. Fails if the key doesn't exist with old_value.
pub fn update(
  self: CSMT,
  key: ByteArray,
  proof: Proof,
  old_value: ByteArray,
  new_value: ByteArray,
) -> CSMT {
  let (old_root, new_root) = including_pair(key, old_value, new_value, proof)
  expect old_root == self.root
  CSMT { root: new_root }
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
  let (without, with) = without_and_with(Some(0), key, value, proof)
  expect with == self.root
  CSMT { root: without }
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
  let (without, with) = without_and_with(Some(1), key, value, proof)
  expect with == self.root
  CSMT { root: without }
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
  let (without, with) = without_and_with(Some(0), key, value, proof)
  expect without == self.root
  CSMT { root: with }
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
  let (without, with) = without_and_with(Some(1), key, value, proof)
  expect without == self.root
  CSMT { root: with }
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

/// The root jump, packed once, after checking that it is exactly the leading
/// bits of the key. The root jump is hashed as given, so any other jump would
/// let the proof of one key stand for another.
fn root_jump_of(key: ByteArray, root_jump: ByteArray) -> ByteArray {
  let count = bytearray.length(root_jump)
  let packed = packed_from_bitpath(root_jump)
  expect packed_slice(key, 0, count) == packed
  packed
}

/// Compute the root hash assuming the key IS present with the given value.
fn including(key: ByteArray, value: ByteArray, proof: Proof) -> ByteArray {
  let jump = root_jump_of(key, proof.root_jump)
  let start = bytearray.length(proof.root_jump)
  let root_value =
    fold_including(
      blake2b_256(value),
      key,
      start,
      8 * bytearray.length(key),
      proof.steps,
    )
  blake2b_256(serialize_packed_indirect(jump, start, root_value))
}

/// Walk proof steps from leaf to root, combining hashes. The key stays packed:
/// positions are bit positions in the whole key. The cursor starts at the end
/// of the key and moves toward `start`, the length of the root jump, where the
/// steps must end: key bits left over would be unhashed. A step consumes at
/// least one bit, the branch bit: the cut of its jump, `consumed - 1` bits,
/// refuses a step that consumes fewer.
fn fold_including(
  acc: ByteArray,
  key: ByteArray,
  start: Int,
  cursor: Int,
  steps: List<ProofStep>,
) -> ByteArray {
  when steps is {
    [] -> {
      expect cursor == start
      acc
    }
    [ProofStep { consumed, sibling: Indirect { jump, hash } }, ..rest] -> {
      let new_cursor = cursor - consumed
      let new_acc =
        combine_step(
          packed_bit(key, new_cursor),
          key,
          new_cursor,
          consumed,
          acc,
          jump,
          hash,
        )
      fold_including(new_acc, key, start, new_cursor, rest)
    }
  }
}

/// The hash of the branch at a step: the key side sits at bit `at` of the key and
/// consumed `consumed` bits, the branch bit and a jump of the bits after it.
/// `direction` is that branch bit, which the caller has read from the key, so
/// that `at` is known to be a position of the key. `acc` is the hash of the node
/// below, a 32-byte digest, and the sibling is given as its jump and its hash.
fn combine_step(
  direction: Int,
  key: ByteArray,
  at: Int,
  consumed: Int,
  acc: ByteArray,
  jump: ByteArray,
  hash: ByteArray,
) -> ByteArray {
  let head =
    if consumed == 1 {
      unjumped_head
    } else {
      serialize_cut_head(key, at + 1, consumed - 1)
    }
  branch_hash(
    direction,
    bytearray.concat(head, acc),
    serialize_sibling(jump, hash),
  )
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------- including + extremum
// -----------------------------------------------------------------------------

/// Like `including`, but asserts every branch direction equals `expected_dir`.
fn including_extremum(
  expected_dir: Int,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> ByteArray {
  let jump = root_jump_of(key, proof.root_jump)
  let start = bytearray.length(proof.root_jump)
  let root_value =
    fold_including_extremum(
      expected_dir,
      blake2b_256(value),
      key,
      start,
      8 * bytearray.length(key),
      proof.steps,
    )
  blake2b_256(serialize_packed_indirect(jump, start, root_value))
}

/// Same as fold_including but expects direction == expected_dir at every step.
fn fold_including_extremum(
  expected_dir: Int,
  acc: ByteArray,
  key: ByteArray,
  start: Int,
  cursor: Int,
  steps: List<ProofStep>,
) -> ByteArray {
  when steps is {
    [] -> {
      expect cursor == start
      acc
    }
    [ProofStep { consumed, sibling: Indirect { jump, hash } }, ..rest] -> {
      let new_cursor = cursor - consumed
      let direction = packed_bit(key, new_cursor)
      expect direction == expected_dir
      let new_acc =
        combine_step(direction, key, new_cursor, consumed, acc, jump, hash)
      fold_including_extremum(
        expected_dir,
        new_acc,
        key,
        start,
        new_cursor,
        rest,
      )
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
/// (the cut of their jump refuses fewer) and end at the start of the key below
/// the root jump, as the including folds require. A lowest step that points
/// outside the key is refused by the bit read or the cut, and a root jump is
/// hashed as given: one that is not the key's can only reproduce the root of a
/// tree that does not hold the key.
///
/// With an `expected_dir`, every branch the key sits at must go that way.
fn do_excluding(
  expected_dir: Option<Int>,
  key: ByteArray,
  proof: Proof,
) -> ByteArray {
  when proof.steps is {
    // No steps: tree is empty without this element
    [] -> null_hash

    // At least one step: collapse the bottom branch
    [bottom_step, ..rest_steps] -> {
      let start = bytearray.length(proof.root_jump)
      let jump = packed_from_bitpath(proof.root_jump)
      let bottom_cursor = 8 * bytearray.length(key) - bottom_step.consumed
      let direction = packed_bit(key, bottom_cursor)
      expect goes(expected_dir, direction)

      when rest_steps is {
        // Collapsed node IS the whole tree
        [] -> {
          let (collapsed_jump, count) =
            collapse(key, start, bottom_cursor, direction, bottom_step)
          blake2b_256(
            serialize_packed_indirect(
              packed_concat(jump, start, collapsed_jump, count),
              start + count,
              bottom_step.sibling.hash,
            ),
          )
        }

        // Use collapsed as our indirect at the next level, then normal
        [next_step, ..upper_steps] -> {
          let next_cursor = bottom_cursor - next_step.consumed
          let next_direction = packed_bit(key, next_cursor)
          expect goes(expected_dir, next_direction)
          let acc =
            collapse_into(
              key,
              bottom_step,
              bottom_cursor,
              direction,
              next_step,
              next_cursor,
              next_direction,
            )
          let root_value =
            when expected_dir is {
              None -> fold_including(acc, key, start, next_cursor, upper_steps)
              Some(dir) ->
                fold_including_extremum(
                  dir,
                  acc,
                  key,
                  start,
                  next_cursor,
                  upper_steps,
                )
            }
          blake2b_256(serialize_packed_indirect(jump, start, root_value))
        }
      }
    }
  }
}

/// The jump of the sibling that takes the removed branch's place, packed, with
/// its bit count: the key bits from `above` (just after the branch bit above)
/// to the removed branch bit, the bit the key did not take, and the sibling's
/// own jump, which the proof carries one byte per bit and is packed here.
fn collapse(
  key: ByteArray,
  above: Int,
  bottom_cursor: Int,
  direction: Int,
  bottom_step: ProofStep,
) -> (ByteArray, Int) {
  let kept = bottom_cursor - above
  let sibling_count = bytearray.length(bottom_step.sibling.jump)
  let head =
    packed_concat(
      packed_slice(key, above, kept),
      kept,
      packed_single(1 - direction),
      1,
    )
  (
    packed_concat(
      head,
      kept + 1,
      packed_from_bitpath(bottom_step.sibling.jump),
      sibling_count,
    ),
    kept + 1 + sibling_count,
  )
}

/// The hash of the sibling that takes the removed branch's place, combined with
/// the next sibling up on the side `next_direction` the key takes.
fn collapse_into(
  key: ByteArray,
  bottom_step: ProofStep,
  bottom_cursor: Int,
  direction: Int,
  next_step: ProofStep,
  next_cursor: Int,
  next_direction: Int,
) -> ByteArray {
  let (collapsed_jump, count) =
    collapse(key, next_cursor + 1, bottom_cursor, direction, bottom_step)
  branch_hash(
    next_direction,
    serialize_packed_indirect(collapsed_jump, count, bottom_step.sibling.hash),
    serialize_sibling(next_step.sibling.jump, next_step.sibling.hash),
  )
}

/// Whether a branch bit is the one an extremum requires, if one is required.
fn goes(expected_dir: Option<Int>, direction: Int) -> Bool {
  when expected_dir is {
    None -> True
    Some(dir) -> direction == dir
  }
}

// -----------------------------------------------------------------------------
// ----------------------------------------------------------------- Both at once
// -----------------------------------------------------------------------------

/// Two walks of the proof from the same position, each from its own hash. The
/// steps, the key side and the siblings are the same, so the jump of the key
/// and the sibling of a step are serialized once for both. With an
/// `expected_dir`, every branch the key sits at must go that way.
fn fold_pair(
  expected_dir: Option<Int>,
  first: ByteArray,
  second: ByteArray,
  key: ByteArray,
  start: Int,
  cursor: Int,
  steps: List<ProofStep>,
) -> (ByteArray, ByteArray) {
  when steps is {
    [] -> {
      expect cursor == start
      (first, second)
    }
    [ProofStep { consumed, sibling: Indirect { jump, hash } }, ..rest] -> {
      let new_cursor = cursor - consumed
      let direction = packed_bit(key, new_cursor)
      expect goes(expected_dir, direction)
      let head =
        if consumed == 1 {
          unjumped_head
        } else {
          serialize_cut_head(key, new_cursor + 1, consumed - 1)
        }
      let theirs = serialize_sibling(jump, hash)
      fold_pair(
        expected_dir,
        branch_hash(direction, bytearray.concat(head, first), theirs),
        branch_hash(direction, bytearray.concat(head, second), theirs),
        key,
        start,
        new_cursor,
        rest,
      )
    }
  }
}

/// The roots of the tree with the key holding each of two values.
fn including_pair(
  key: ByteArray,
  first_value: ByteArray,
  second_value: ByteArray,
  proof: Proof,
) -> (ByteArray, ByteArray) {
  let jump = root_jump_of(key, proof.root_jump)
  let start = bytearray.length(proof.root_jump)
  let (first, second) =
    fold_pair(
      None,
      blake2b_256(first_value),
      blake2b_256(second_value),
      key,
      start,
      8 * bytearray.length(key),
      proof.steps,
    )
  (
    blake2b_256(serialize_packed_indirect(jump, start, first)),
    blake2b_256(serialize_packed_indirect(jump, start, second)),
  )
}

/// `including`, with every branch required to go `expected_dir` when there is one.
fn including_with(
  expected_dir: Option<Int>,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> ByteArray {
  when expected_dir is {
    None -> including(key, value, proof)
    Some(dir) -> including_extremum(dir, key, value, proof)
  }
}

/// The roots of the tree without the key and of the tree with the key holding
/// `value`. A proof of two steps or more is walked once for both, from where the
/// lowest two steps leave each of them; a shorter one is walked twice. With an
/// `expected_dir`, every branch the key sits at must go that way.
fn without_and_with(
  expected_dir: Option<Int>,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> (ByteArray, ByteArray) {
  when proof.steps is {
    [bottom_step, next_step, ..upper_steps] -> {
      let jump = root_jump_of(key, proof.root_jump)
      let start = bytearray.length(proof.root_jump)
      let bottom_cursor = 8 * bytearray.length(key) - bottom_step.consumed
      let direction = packed_bit(key, bottom_cursor)
      expect goes(expected_dir, direction)
      let next_cursor = bottom_cursor - next_step.consumed
      let next_direction = packed_bit(key, next_cursor)
      expect goes(expected_dir, next_direction)
      let without =
        collapse_into(
          key,
          bottom_step,
          bottom_cursor,
          direction,
          next_step,
          next_cursor,
          next_direction,
        )
      let with =
        combine_step(
          next_direction,
          key,
          next_cursor,
          next_step.consumed,
          combine_step(
            direction,
            key,
            bottom_cursor,
            bottom_step.consumed,
            blake2b_256(value),
            bottom_step.sibling.jump,
            bottom_step.sibling.hash,
          ),
          next_step.sibling.jump,
          next_step.sibling.hash,
        )
      let (without_value, with_value) =
        fold_pair(
          expected_dir,
          without,
          with,
          key,
          start,
          next_cursor,
          upper_steps,
        )
      (
        blake2b_256(serialize_packed_indirect(jump, start, without_value)),
        blake2b_256(serialize_packed_indirect(jump, start, with_value)),
      )
    }
    _ ->
      (
        do_excluding(expected_dir, key, proof),
        including_with(expected_dir, key, value, proof),
      )
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
