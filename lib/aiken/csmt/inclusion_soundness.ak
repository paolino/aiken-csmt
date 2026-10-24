//// No inclusion proof, however malformed, makes a false membership statement
//// verify. Rejection is `False` or a failed script, so every rejection
//// property is a `fail` test: it passes when the verifier refuses every
//// generated statement.

use aiken/collection/list
use aiken/csmt.{
  CSMT, Proof, ProofStep, delete, from_root, has, pop, pop_max, root, update,
}
use aiken/csmt/malformed.{
  absent_key_statement, false_statement, honest_statement,
  other_length_key_statement, wrong_value_statement,
}
use aiken/csmt/reference.{branch_preimages, proof_of, root_of}
use aiken/primitive/bytearray

/// The result of an accepted removal, used so that it is evaluated: an unused
/// `let` is erased and its failure would never run.
fn accepted(trie: CSMT) -> Bool {
  bytearray.length(root(trie)) == 32
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------ Properties
// -----------------------------------------------------------------------------

// Control: the proofs the generators damage are accepted when left alone.
test prop_honest_proof_is_accepted(statement via honest_statement()) {
  has(statement.trie, statement.key, statement.value, statement.proof)
}

test prop_has_rejects_wrong_value(statement via wrong_value_statement()) fail {
  has(statement.trie, statement.key, statement.value, statement.proof)
}

// A key of the tree's length that the tree does not hold, with any value.
test prop_has_rejects_absent_key(statement via absent_key_statement()) fail {
  has(statement.trie, statement.key, statement.value, statement.proof)
}

// A key longer or shorter than the tree's keys, with any value that is not a
// branch preimage of the tree. A branch preimage as the value of a shorter key
// verifies: the node hash does not tell a leaf from a branch, so the tree's
// key length is an obligation of the caller (see the module documentation of
// `aiken/csmt`).
test prop_has_rejects_other_length_key(
  statement via other_length_key_statement(),
) fail {
  has(statement.trie, statement.key, statement.value, statement.proof)
}

test prop_delete_rejects_false_membership(statement via false_statement()) fail {
  accepted(
    delete(statement.trie, statement.key, statement.value, statement.proof),
  )
}

test prop_update_rejects_false_membership(statement via false_statement()) fail {
  accepted(
    update(statement.trie, statement.key, statement.proof, statement.value, #""),
  )
}

test prop_pop_rejects_false_membership(statement via false_statement()) fail {
  accepted(pop(statement.trie, statement.key, statement.value, statement.proof))
}

test prop_pop_max_rejects_false_membership(statement via false_statement()) fail {
  accepted(
    pop_max(statement.trie, statement.key, statement.value, statement.proof),
  )
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------ Counterexamples kept
// -----------------------------------------------------------------------------
// Each statement below is false and was verified before the range checks.

// Generator: the proof of ab offered for 2b, which differs from ab inside the
// root jump.
test has_rejects_root_jump_that_differs_from_key() fail {
  let entries = [(#"ab", #"cd")]
  has(from_root(root_of(entries)), #"2b", #"cd", proof_of(entries, #"ab"))
}

// The probe of the issue: the proof of 01 offered for 02.
test has_rejects_proof_of_the_neighbouring_key() fail {
  let entries = [(#"01", #"cafe")]
  has(from_root(root_of(entries)), #"02", #"cafe", proof_of(entries, #"01"))
}

test delete_rejects_proof_of_the_neighbouring_key() fail {
  let entries = [(#"01", #"cafe")]
  accepted(
    delete(
      from_root(root_of(entries)),
      #"02",
      #"cafe",
      proof_of(entries, #"01"),
    ),
  )
}

test update_rejects_proof_of_the_neighbouring_key() fail {
  let entries = [(#"01", #"cafe")]
  accepted(
    update(
      from_root(root_of(entries)),
      #"02",
      proof_of(entries, #"01"),
      #"cafe",
      #"beef",
    ),
  )
}

test pop_rejects_proof_of_the_neighbouring_key() fail {
  let entries = [(#"01", #"cafe")]
  accepted(
    pop(from_root(root_of(entries)), #"02", #"cafe", proof_of(entries, #"01")),
  )
}

test pop_max_rejects_proof_of_the_neighbouring_key() fail {
  let entries = [(#"01", #"cafe")]
  accepted(
    pop_max(
      from_root(root_of(entries)),
      #"02",
      #"cafe",
      proof_of(entries, #"01"),
    ),
  )
}

// Generator: the proof of ab offered for the extension ab01, whose last byte
// the steps never reach.
test has_rejects_extension_of_held_key() fail {
  let entries = [(#"ab", #"cd")]
  has(from_root(root_of(entries)), #"ab01", #"cd", proof_of(entries, #"ab"))
}

// Generator: the keys 0000, 8000, 0100 and 0080 branch at bits 0, 7 and 8 of
// 0000. The proof of 0000 with its single-bit step consuming -7 reads the last
// bit of 00 again, so the key 00, one byte shorter, yields the root.
test has_rejects_shorter_key_read_through_a_negative_step() fail {
  let entries = [(#"0000", #""), (#"8000", #""), (#"0100", #""), (#"0080", #"")]
  expect [bottom, single_bit, top] = proof_of(entries, #"0000").steps
  has(
    from_root(root_of(entries)),
    #"00",
    #"",
    Proof {
      root_jump: #"",
      steps: [bottom, ProofStep { ..single_bit, consumed: -7 }, top],
    },
  )
}

// Generator: ten keys branching off 0000 at bits 0 to 8. The proof of 0000
// with its eight single-bit steps consuming nothing reads the first bit of 00
// eight times.
test has_rejects_shorter_key_read_through_steps_that_consume_nothing() fail {
  let entries =
    [
      (#"0000", #""), (#"8000", #""), (#"4000", #""), (#"2000", #""),
      (#"1000", #""), (#"0800", #""), (#"0400", #""), (#"0200", #""),
      (#"0100", #""), (#"0080", #""),
    ]
  let honest = proof_of(entries, #"0000")
  has(
    from_root(root_of(entries)),
    #"00",
    #"",
    Proof {
      root_jump: #"",
      steps: list.map(
        honest.steps,
        fn(step) {
          if step.consumed == 1 {
            ProofStep { ..step, consumed: 0 }
          } else {
            step
          }
        },
      ),
    },
  )
}

// Generator: the held key 00 claimed with the serialized pair of the root's
// children as its value and no steps at all, so that no bit of the key is
// hashed. The key has the tree's own length, so the statement is false.
test has_rejects_branch_preimage_as_value_of_a_held_key() fail {
  let entries = [(#"00", #"aa"), (#"80", #"bb")]
  expect [preimage, ..] = branch_preimages(entries)
  has(
    from_root(root_of(entries)),
    #"00",
    preimage,
    Proof { root_jump: #"", steps: [] },
  )
}

// The keys 00 and 01 share seven bits, so the root jump is those seven bits and
// the root node branches on the last one. The held key 00, claimed with the
// serialized pair of the root's children and no steps, leaves its last bit
// unhashed.
test has_rejects_branch_preimage_with_one_key_bit_unhashed() fail {
  let entries = [(#"00", #"aa"), (#"01", #"bb")]
  expect [preimage, ..] = branch_preimages(entries)
  has(
    from_root(root_of(entries)),
    #"00",
    preimage,
    Proof { root_jump: #[0, 0, 0, 0, 0, 0, 0], steps: [] },
  )
}
