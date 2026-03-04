//// A Compact Sparse Merkle Trie (CSMT) is a key:value structure similar to
//// a Merkle Patricia Forestry, but where keys are NOT hashed before insertion.
////
//// This preserves key ordering in the trie, enabling use cases like FIFO
//// queues where insertion order matters and non-existence proofs can
//// demonstrate that no key smaller than a given value exists.
////
//// The trie uses radix 16 (hexadecimal nibbles). Values are still hashed
//// with blake2b_256 for compact commitment.
////
//// ## Differences from MPF
////
//// - Keys are used directly as trie paths (not hashed)
//// - Key ordering is preserved in the trie structure
//// - Variable-length keys are supported
//// - Non-existence proofs can reason about ordering

use aiken/builtin.{blake2b_256, slice_bytearray}
use aiken/csmt/helpers.{combine, nibble, nibbles, suffix}
use aiken/csmt/merkling.{merkle_16, null_hash, sparse_merkle_16}
use aiken/primitive/bytearray

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------- Constants
// -----------------------------------------------------------------------------

/// # of bytes
const blake2b_256_digest_size = 32

// -----------------------------------------------------------------------------
// ------------------------------------------------- Compact Sparse Merkle Trie
// -----------------------------------------------------------------------------

/// A Compact Sparse Merkle Trie, typically constructed from a root hash digest
/// using [`from_root`](#from_root).
pub opaque type CSMT {
  root: ByteArray,
}

// ## Constructing

/// Construct a new [CSMT](#CSMT) from its root.
///
/// The root MUST be 32-bytes long. For an empty trie, see [empty](#empty).
pub fn from_root(root: ByteArray) -> CSMT {
  expect bytearray.length(root) == blake2b_256_digest_size
  CSMT { root }
}

/// Construct a new empty [CSMT](#CSMT).
pub const empty: CSMT = CSMT { root: null_hash }

// ## Querying

/// Check whether a [CSMT](#CSMT) is empty.
pub fn is_empty(self: CSMT) -> Bool {
  self.root == null_hash
}

/// Test whether an element is present in the trie with a specific value.
pub fn has(
  self: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> Bool {
  including(key, value, proof) == self.root
}

/// Test whether a key is missing from the trie.
pub fn miss(self: CSMT, key: ByteArray, proof: Proof) -> Bool {
  excluding(key, proof) == self.root
}

// # Modifying

/// Insert an element in the trie.
///
/// #### Fails when
///
/// - The [Proof](#Proof) is invalid.
/// - There's already an element in the trie at the given key.
pub fn insert(
  self: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> CSMT {
  expect excluding(key, proof) == self.root
  CSMT { root: including(key, value, proof) }
}

/// Remove an element from the trie.
///
/// #### Fails when
///
/// - the [Proof](#Proof) is invalid
/// - there is no element in the trie at the given key
pub fn delete(
  self: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> CSMT {
  expect including(key, value, proof) == self.root
  CSMT { root: excluding(key, proof) }
}

/// Update an element in the trie with a new value.
///
/// #### Fails when
///
/// - The [Proof](#Proof) is invalid.
/// - There's no element in the trie at the given key.
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

// ## Transforming

/// Get the root hash digest of a [CSMT](#CSMT).
pub fn root(self: CSMT) -> ByteArray {
  self.root
}

// -----------------------------------------------------------------------------
// ----------------------------------------------------------------------- Proof
// -----------------------------------------------------------------------------

/// A Proof is a list of steps processed from left to right, corresponding
/// to neighbor nodes along the path to the element being proved.
pub type Proof =
  List<ProofStep>

/// Three kinds of proof steps: Branch, Fork and Leaf.
pub type ProofStep {
  Branch { skip: Int, neighbors: ByteArray }
  Fork { skip: Int, neighbor: Neighbor }
  Leaf { skip: Int, key: ByteArray, value: ByteArray }
}

/// A neighbor node used in a proof.
pub type Neighbor {
  nibble: Int,
  prefix: ByteArray,
  root: ByteArray,
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------- including
// -----------------------------------------------------------------------------

/// Compute the resulting hash digest from a Proof associated with an
/// arbitrary value. Unlike MPF, the key is NOT hashed — it is used
/// directly as the trie path.
fn including(key: ByteArray, value: ByteArray, proof: Proof) -> ByteArray {
  do_including(key, blake2b_256(value), 0, proof)
}

test including_empty_proof() {
  let (k, v) = (#"0102", "bar")
  including(k, v, []) == combine(suffix(k, 0), blake2b_256(v))
}

fn do_including(
  path: ByteArray,
  value: ByteArray,
  cursor: Int,
  proof: Proof,
) -> ByteArray {
  when proof is {
    [] -> combine(suffix(path, cursor), value)

    [Branch { skip, neighbors }, ..steps] -> {
      let next_cursor = cursor + skip
      let root = do_including(path, value, next_cursor + 1, steps)
      do_branch(path, cursor, next_cursor, root, neighbors)
    }

    [Fork { skip, neighbor }, ..steps] -> {
      let next_cursor = cursor + skip
      let root = do_including(path, value, next_cursor + 1, steps)
      do_fork(path, cursor, next_cursor, root, neighbor)
    }

    [Leaf { skip, key, value: neighbor_value }, ..steps] -> {
      let next_cursor = cursor + skip
      let root = do_including(path, value, next_cursor + 1, steps)

      let neighbor =
        Neighbor {
          prefix: suffix(key, next_cursor + 1),
          nibble: nibble(key, next_cursor),
          root: neighbor_value,
        }

      do_fork(path, cursor, next_cursor, root, neighbor)
    }
  }
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------- excluding
// -----------------------------------------------------------------------------

/// Similar to including, but computes the root obtained from walking the
/// proof without including the element. Key is NOT hashed.
fn excluding(key: ByteArray, proof: Proof) -> ByteArray {
  do_excluding(key, 0, proof)
}

test excluding_empty_proof() {
  excluding(#"0102", []) == empty.root
}

fn do_excluding(path: ByteArray, cursor: Int, proof: Proof) -> ByteArray {
  when proof is {
    [] -> null_hash

    [Branch { skip, neighbors }, ..steps] -> {
      let next_cursor = cursor + skip
      let root = do_excluding(path, next_cursor + 1, steps)
      do_branch(path, cursor, next_cursor, root, neighbors)
    }

    [Fork { skip, neighbor }] -> {
      let neighbor_prefix = bytearray.push(neighbor.prefix, neighbor.nibble)
      let prefix =
        if skip == 0 {
          neighbor_prefix
        } else {
          bytearray.concat(
            nibbles(path, cursor, cursor + skip),
            neighbor_prefix,
          )
        }
      combine(prefix, neighbor.root)
    }

    [Fork { skip, neighbor }, ..steps] -> {
      let next_cursor = cursor + skip
      let root = do_excluding(path, next_cursor + 1, steps)
      do_fork(path, cursor, next_cursor, root, neighbor)
    }

    [Leaf { key, value, .. }] -> combine(suffix(key, cursor), value)

    [Leaf { skip, key, value }, ..steps] -> {
      let next_cursor = cursor + skip
      let root = do_excluding(path, next_cursor + 1, steps)

      let neighbor =
        Neighbor {
          prefix: suffix(key, next_cursor + 1),
          nibble: nibble(key, next_cursor),
          root: value,
        }

      do_fork(path, cursor, next_cursor, root, neighbor)
    }
  }
}

// -----------------------------------------------------------------------------
// --------------------------------------------------------- do_branch / do_fork
// -----------------------------------------------------------------------------

fn do_branch(
  path: ByteArray,
  cursor: Int,
  next_cursor: Int,
  root: ByteArray,
  neighbors: ByteArray,
) -> ByteArray {
  let branch = nibble(path, next_cursor)

  let prefix = nibbles(path, cursor, next_cursor)

  let select =
    slice_bytearray(_, blake2b_256_digest_size, neighbors)

  combine(
    prefix,
    merkle_16(branch, root, select(0), select(32), select(64), select(96)),
  )
}

fn do_fork(
  path: ByteArray,
  cursor: Int,
  next_cursor: Int,
  root: ByteArray,
  neighbor: Neighbor,
) -> ByteArray {
  let branch = nibble(path, next_cursor)

  let prefix = nibbles(path, cursor, next_cursor)

  expect branch != neighbor.nibble

  combine(
    prefix,
    sparse_merkle_16(
      branch,
      root,
      neighbor.nibble,
      combine(neighbor.prefix, neighbor.root),
    ),
  )
}
