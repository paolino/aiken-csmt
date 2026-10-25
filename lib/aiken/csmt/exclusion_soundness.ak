//// No exclusion proof, however malformed, makes a tree that holds a key claim
//// not to hold it. Rejection is `False` or a failed script, so every rejection
//// property is a `fail` test: it passes when the verifier refuses every
//// generated statement.

use aiken/builtin.{blake2b_256}
use aiken/csmt.{
  CSMT, Proof, ProofStep, from_root, insert, miss, push_max, push_min, root,
}
use aiken/csmt/bits.{pack_bits}
use aiken/csmt/hashing.{Indirect}
use aiken/csmt/malformed.{
  absorbing, carrying, held_key_statement, held_maximum_statement,
  held_minimum_statement, honest_insertion, honest_maximum_insertion,
  honest_minimum_insertion, non_maximum_insertion, non_minimum_insertion,
  with_a_sibling_jump_byte_above_one,
}
use aiken/csmt/reference.{proof_of, root_of}
use aiken/fuzz
use aiken/primitive/bytearray

/// The result of an accepted insertion, used so that it is evaluated: an unused
/// `let` is erased and its failure would never run.
fn accepted(trie: CSMT) -> Bool {
  bytearray.length(root(trie)) == 32
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------ Properties
// -----------------------------------------------------------------------------

// Control: the proofs the generators damage are accepted when left alone, and
// the insertion they authorise reaches the root the reference trie computes.
test prop_honest_exclusion_is_accepted(insertion via honest_insertion()) {
  miss(insertion.before, insertion.key, insertion.proof) && root(
    insert(insertion.before, insertion.key, insertion.value, insertion.proof),
  ) == insertion.after
}

test prop_honest_push_min_is_accepted(insertion via honest_minimum_insertion()) {
  root(
    push_min(insertion.before, insertion.key, insertion.value, insertion.proof),
  ) == insertion.after
}

test prop_honest_push_max_is_accepted(insertion via honest_maximum_insertion()) {
  root(
    push_max(insertion.before, insertion.key, insertion.value, insertion.proof),
  ) == insertion.after
}

test prop_miss_rejects_held_key(statement via held_key_statement()) fail {
  miss(statement.trie, statement.key, statement.proof)
}

test prop_insert_rejects_held_key(statement via held_key_statement()) fail {
  accepted(
    insert(statement.trie, statement.key, statement.value, statement.proof),
  )
}

test prop_push_min_rejects_held_key(
  statement via fuzz.either(held_key_statement(), held_minimum_statement()),
) fail {
  accepted(
    push_min(statement.trie, statement.key, statement.value, statement.proof),
  )
}

test prop_push_max_rejects_held_key(
  statement via fuzz.either(held_key_statement(), held_maximum_statement()),
) fail {
  accepted(
    push_max(statement.trie, statement.key, statement.value, statement.proof),
  )
}

// The variants walk the same path as `insert` and only add the direction every
// branch must take: a key that is not the smallest (largest) is refused by
// push_min (push_max) even when its proof is honest.
test prop_push_min_rejects_a_key_that_is_not_the_minimum(
  insertion via non_minimum_insertion(),
) fail {
  accepted(
    push_min(insertion.before, insertion.key, insertion.value, insertion.proof),
  )
}

test prop_push_max_rejects_a_key_that_is_not_the_maximum(
  insertion via non_maximum_insertion(),
) fail {
  accepted(
    push_max(insertion.before, insertion.key, insertion.value, insertion.proof),
  )
}

// -----------------------------------------------------------------------------
// ----------------------------------------------------------------- Reliance
// -----------------------------------------------------------------------------
// The verifier reads the direction of a bottom step at the key position its
// `consumed` points to, and relies on the builtin to refuse a position outside
// the key, so that a bottom step that consumes nothing, or more than the key
// has, needs no range check of its own.

test index_past_the_key_fails() fail {
  bytearray.at(#"01", 1) == 0
}

test index_before_the_key_fails() fail {
  bytearray.at(#"01", -1) == 0
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------ Counterexamples kept
// -----------------------------------------------------------------------------
// Each statement below was verified before the checks of this module. The
// proofs are built from the reference trie, never typed: `absorbing` puts a
// node of the tree on the key's path, with its first jump bit dropped, in the
// sibling of the bottom step, and the bit the verifier prepends when it
// collapses the branch gives that node back.

// The proof of the issue: the only key of the tree, offered as the sibling of a
// bottom step that reads bit 4 and consumes the last four bits, so that the
// first four bits of the key are never hashed.
test miss_rejects_a_bottom_step_that_leaves_key_bits_unhashed() fail {
  let entries = [(#"0f", #"cafe")]
  miss(
    from_root(root_of(entries)),
    #"0f",
    absorbing(entries, #"0f", -1, 0, 4, 1, 0),
  )
}

// The same on a tree of two keys that share sixteen bits: the whole tree is
// the sibling, and the step reads bit 2.
test miss_rejects_a_bottom_step_that_leaves_bits_unhashed_in_a_larger_tree() fail {
  let entries = [(#"202020", #""), (#"202080", #"")]
  miss(
    from_root(root_of(entries)),
    #"202020",
    absorbing(entries, #"202020", -1, 0, 2, 1, 0),
  )
}

// The leaf of 03 is the sibling of a bottom step that reads bit 6 of the key,
// six bits below the branch bit of the step above. The collapsed branch must
// keep the bits between the two branch bits: without them the sibling is the
// leaf itself, and the claim that the leaf is absent verifies.
test miss_rejects_a_leaf_absorbed_below_the_branch_bit() fail {
  let entries = [(#"03", #""), (#"80", #"")]
  miss(
    from_root(root_of(entries)),
    #"03",
    absorbing(entries, #"03", 0, 0, 6, 1, 0),
  )
}

test insert_rejects_a_leaf_absorbed_below_the_branch_bit() fail {
  let entries = [(#"03", #""), (#"80", #"")]
  accepted(
    insert(
      from_root(root_of(entries)),
      #"03",
      #"",
      absorbing(entries, #"03", 0, 0, 6, 1, 0),
    ),
  )
}

test push_min_rejects_a_node_absorbed_below_the_branch_bit() fail {
  let entries = [(#"50", #""), (#"60", #""), (#"51", #"")]
  accepted(
    push_min(
      from_root(root_of(entries)),
      #"50",
      #"",
      absorbing(entries, #"50", 0, 0, 4, 1, 0),
    ),
  )
}

test push_max_rejects_a_leaf_absorbed_below_the_branch_bit() fail {
  let entries = [(#"2121", #""), (#"0000", #"")]
  accepted(
    push_max(
      from_root(root_of(entries)),
      #"2121",
      #"",
      absorbing(entries, #"2121", 0, 0, 13, 1, 0),
    ),
  )
}

// The step above the bottom step consumes nothing, so the bottom step and the
// branch above it read the same bit: the first jump bit of the leaf of 40 is
// the opposite of the bit it reads, and the collapse gives the leaf back.
test miss_rejects_a_step_that_consumes_nothing_above_the_bottom_step() fail {
  let entries = [(#"40", #""), (#"80", #"")]
  miss(
    from_root(root_of(entries)),
    #"40",
    absorbing(entries, #"40", 0, 0, 0, 1, 0),
  )
}

// The honest proofs of a key whose neighbour hangs below a compressed jump:
// 00 joins 01 under a jump of six bits, itself the left child of the root.
test insert_accepts_a_key_that_joins_a_node_below_a_compressed_jump() {
  let entries = [(#"00", #"cc"), (#"01", #"aa"), (#"80", #"bb")]
  root(
    insert(
      from_root(root_of([(#"01", #"aa"), (#"80", #"bb")])),
      #"00",
      #"cc",
      proof_of(entries, #"00"),
    ),
  ) == root_of(entries)
}

test push_min_accepts_a_key_that_joins_a_node_below_a_compressed_jump() {
  let entries = [(#"00", #"cc"), (#"01", #"aa"), (#"80", #"bb")]
  root(
    push_min(
      from_root(root_of([(#"01", #"aa"), (#"80", #"bb")])),
      #"00",
      #"cc",
      proof_of(entries, #"00"),
    ),
  ) == root_of(entries)
}

test push_max_accepts_a_key_that_joins_a_node_below_a_compressed_jump() {
  let entries = [(#"00", #"aa"), (#"fe", #"bb"), (#"ff", #"cc")]
  root(
    push_max(
      from_root(root_of([(#"00", #"aa"), (#"fe", #"bb")])),
      #"ff",
      #"cc",
      proof_of(entries, #"ff"),
    ),
  ) == root_of(entries)
}

// The only key of the tree is 80, which is the bits 1 and seven 0. The lowest
// sibling's jump starts with the byte 2, which packs as the value 2 and so
// adds 1 to the bit before it: the collapse prepends the bit 0 to the jump, and
// the eight bytes 0, 2, 0 … 0 pack to 80, the key's own path. The jump is as
// long as the key's path minus the removed bit, so the root hash is the one of
// the tree that holds the key.
test miss_rejects_a_sibling_jump_that_carries_into_the_removed_bit() fail {
  let entries = [(#"80", #"")]
  miss(
    from_root(root_of(entries)),
    #"80",
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 8,
          sibling: Indirect {
            jump: #[2, 0, 0, 0, 0, 0, 0],
            hash: blake2b_256(#""),
          },
        },
      ],
    },
  )
}

// The same on a tree of two keys, as a lowest step below a branch bit and with
// a carry of four places.
test miss_rejects_a_sibling_jump_that_carries_into_the_removed_bit_below_a_branch() fail {
  let entries = [(#"c0", #""), (#"00", #"")]
  miss(
    from_root(root_of(entries)),
    #"c0",
    carrying(absorbing(entries, #"c0", 0, 0, 1, 1, 0), 4),
  )
}

// A byte above 1 in a jump is refused where jumps are packed, whatever the
// jump is concatenated with.
test pack_bits_refuses_a_byte_above_one() fail {
  pack_bits(#[0, 2]) == pack_bits(#[1, 0])
}

// A byte above 1 in the jump of the lowest sibling is refused where the jump is
// packed, though the proof would pack as the honest one without the check.
// The control is the same statement with the honest proof.
test miss_accepts_the_proof_of_a_held_key() {
  let entries = [(#"c0", #""), (#"00", #"")]
  miss(from_root(root_of([(#"00", #"")])), #"c0", proof_of(entries, #"c0"))
}

test miss_rejects_a_sibling_jump_byte_above_one() fail {
  let entries = [(#"c0", #""), (#"00", #"")]
  miss(
    from_root(root_of([(#"00", #"")])),
    #"c0",
    with_a_sibling_jump_byte_above_one(proof_of(entries, #"c0")),
  )
}
