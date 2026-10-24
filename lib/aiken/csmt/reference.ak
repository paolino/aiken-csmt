//// Reference trie for the soundness properties (test-only).
////
//// Builds the root hash and the honest inclusion proof of any set of
//// equal-length keys straight from the haskell-mts definition: every node is
//// an `Indirect` (jump and hash), a branch hashes its two children with
//// `combine_hash`, the root is `root_hash` of the top node. The committed
//// haskell-mts vectors pin it to the reference implementation.

use aiken/builtin.{blake2b_256, slice_bytearray}
use aiken/collection/list
use aiken/csmt.{Proof, ProofStep}
use aiken/csmt/bits.{key_to_bitpath}
use aiken/csmt/hashing.{
  Indirect, combine_hash, null_hash, root_hash, serialize_indirect,
}
use aiken/math
use aiken/primitive/bytearray

/// The key-value pairs a tree holds; all keys have one length.
pub type Entries =
  List<(ByteArray, ByteArray)>

/// A held key as a bit path, with the hash of its value.
type Held {
  bits: ByteArray,
  leaf_hash: ByteArray,
}

fn held(entries: Entries) -> List<Held> {
  list.map(
    entries,
    fn(entry) {
      let (key, value) = entry
      Held { bits: key_to_bitpath(key), leaf_hash: blake2b_256(value) }
    },
  )
}

/// Root hash of the tree holding `entries`.
pub fn root_of(entries: Entries) -> ByteArray {
  when entries is {
    [] -> null_hash
    _ -> {
      let top = node(held(entries))
      root_hash(top.jump, top.hash)
    }
  }
}

/// The indirect of the node holding `leaves`, which are not empty.
fn node(leaves: List<Held>) -> Indirect {
  when leaves is {
    [] -> fail @"empty node"
    [only] -> Indirect { jump: only.bits, hash: only.leaf_hash }
    [first, ..] -> {
      let shared = shared_length(leaves)
      let (left, right) = split(leaves, shared)
      Indirect {
        jump: slice_bytearray(0, shared, first.bits),
        hash: combine_hash(node(left), node(right)),
      }
    }
  }
}

/// Number of leading bits that all `leaves` have in common.
fn shared_length(leaves: List<Held>) -> Int {
  expect [first, ..rest] = leaves
  list.foldl(
    rest,
    bytearray.length(first.bits),
    fn(other, shortest) {
      math.min(shortest, prefix_length(first.bits, other.bits, 0))
    },
  )
}

fn prefix_length(a: ByteArray, b: ByteArray, at: Int) -> Int {
  if at >= bytearray.length(a) || at >= bytearray.length(b) {
    at
  } else if bytearray.at(a, at) == bytearray.at(b, at) {
    prefix_length(a, b, at + 1)
  } else {
    at
  }
}

/// Split by the bit after `shared`, dropping the shared bits and that bit.
fn split(leaves: List<Held>, shared: Int) -> (List<Held>, List<Held>) {
  let (left, right) =
    list.partition(leaves, fn(leaf) { bytearray.at(leaf.bits, shared) == 0 })
  (drop_bits(left, shared + 1), drop_bits(right, shared + 1))
}

fn drop_bits(leaves: List<Held>, count: Int) -> List<Held> {
  list.map(
    leaves,
    fn(leaf) { Held { ..leaf, bits: bytearray.drop(leaf.bits, count) } },
  )
}

/// The honest inclusion proof of `key`, which `entries` hold.
pub fn proof_of(entries: Entries, key: ByteArray) -> Proof {
  let (root_jump, steps) = walk(held(entries), key_to_bitpath(key))
  Proof { root_jump, steps }
}

/// The jump of the node holding `leaves` and the proof steps below it, from
/// the leaf upwards. `path` is the bit path of the proved key from this node.
fn walk(leaves: List<Held>, path: ByteArray) -> (ByteArray, List<ProofStep>) {
  when leaves is {
    [] -> fail @"empty node"
    [only] -> (only.bits, [])
    [first, ..] -> {
      let shared = shared_length(leaves)
      let (left, right) = split(leaves, shared)
      let (mine, other) =
        if bytearray.at(path, shared) == 0 {
          (left, right)
        } else {
          (right, left)
        }
      let rest = bytearray.drop(path, shared + 1)
      let (child_jump, below) = walk(mine, rest)
      let step =
        ProofStep {
          consumed: 1 + bytearray.length(child_jump),
          sibling: node(other),
        }
      (slice_bytearray(0, shared, first.bits), list.concat(below, [step]))
    }
  }
}

/// Every internal node's preimage: the serialized pair of its children, which
/// is also the value that hashes to the node.
pub fn branch_preimages(entries: Entries) -> List<ByteArray> {
  when entries is {
    [] -> []
    _ -> do_preimages(held(entries))
  }
}

fn do_preimages(leaves: List<Held>) -> List<ByteArray> {
  when leaves is {
    [] -> []
    [_] -> []
    _ -> {
      let (left, right) = split(leaves, shared_length(leaves))
      [
        bytearray.concat(
          serialize_indirect(node(left)),
          serialize_indirect(node(right)),
        ),
        ..list.concat(do_preimages(left), do_preimages(right))
      ]
    }
  }
}

/// Every node's indirect, for building proof steps from real siblings.
pub fn node_indirects(entries: Entries) -> List<Indirect> {
  when entries is {
    [] -> []
    _ -> do_indirects(held(entries))
  }
}

fn do_indirects(leaves: List<Held>) -> List<Indirect> {
  when leaves is {
    [] -> []
    [_] -> [node(leaves)]
    _ -> {
      let (left, right) = split(leaves, shared_length(leaves))
      [node(leaves), ..list.concat(do_indirects(left), do_indirects(right))]
    }
  }
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------ haskell-mts agreement
// -----------------------------------------------------------------------------

/// The trees of the committed haskell-mts vectors, with the root hash
/// haskell-mts computes for each of them.
pub fn vector_trees() -> List<(Entries, ByteArray)> {
  [
    (
      [(#"ab", #"cd")],
      #"9a45be5c807ec78e51e2676529adf0dd38cbc0a148e19a6117b4d0bc62a8b844",
    ),
    (
      [(#"00", #"aa"), (#"80", #"bb")],
      #"11abc6871031864533c39361919fa24379b73cbeebf789a0863684101905c0c1",
    ),
    (
      [(#"ab00", #"11"), (#"ab80", #"22")],
      #"048bc31b759974033c09d0c7d3728f9fee50afeb184da66dfe86d6041a23fd57",
    ),
    (
      [(#"00", #"01"), (#"40", #"02"), (#"80", #"03")],
      #"c79caacc79c111a2b4ed0f19fe832b7d4673f2b7dd3505bbc6beb82b3be6ba0b",
    ),
    (
      [(#"00", #"10"), (#"40", #"20"), (#"80", #"30"), (#"c0", #"40")],
      #"1faeb5ccbeebe31365b83f192c005c3f40df7049bf676deaf027a0649937d770",
    ),
    (
      [(#"10", #"aa")],
      #"776f184b5e95aa8d39580b72b09afff2e4c34094bd6235e1a878623fc723e04d",
    ),
    (
      [(#"10", #"aa"), (#"20", #"bb")],
      #"b5e5debcb4ce43a54369142c7aef05fb6d499c43add0f9494bea2b65eafe6948",
    ),
    (
      [(#"42", #"ff")],
      #"63e8a76461d8dfbecf669ce222cd96b69876a4caea4fd94a178dc0bd60e4bf2e",
    ),
    (
      [(#"00", #"aa")],
      #"4ec799b000855432de3e3292057fec1688f983d084747ec87b14953fdaafda98",
    ),
    (
      [(#"ff", #"aa")],
      #"ff775584d13aa234636207200670f7ac1deeacf707d66bfcf0e1f351e41babe3",
    ),
    (
      [(#"40", #"02"), (#"80", #"03")],
      #"e8b8031832e17478c639e02b18c24661b570e615954ef057a4aa2fa51593f709",
    ),
    (
      [(#"00", #"01"), (#"40", #"02")],
      #"97d69470fa45efe64cfbd88897c5304888322e6ebbfe2b7296f7503246e645ed",
    ),
  ]
}

test reference_root_matches_haskell_mts() {
  list.all(
    vector_trees(),
    fn(vector) {
      let (entries, committed) = vector
      root_of(entries) == committed
    },
  )
}

test reference_proofs_verify_against_haskell_mts_roots() {
  list.all(
    vector_trees(),
    fn(vector) {
      let (entries, committed) = vector
      list.all(
        entries,
        fn(entry) {
          let (key, value) = entry
          csmt.has(
            csmt.from_root(committed),
            key,
            value,
            proof_of(entries, key),
          )
        },
      )
    },
  )
}
