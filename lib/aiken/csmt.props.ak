use aiken/builtin.{blake2b_256, slice_bytearray}
use aiken/csmt.{
  Proof, ProofStep, empty, from_root, insert, is_empty, pop, pop_max, push_max,
  push_min, root,
}
use aiken/csmt/bits.{key_to_bitpath}
use aiken/csmt/hashing.{Indirect, combine_hash, root_hash}
use aiken/fuzz

// ---------------------------------------------------------------------------
// ------------------------------------------------ Single-element properties
// ---------------------------------------------------------------------------

// A single element is both min and max → pop and pop_max both give empty.
test prop_single_is_both_min_and_max(v via fuzz.bytearray()) {
  let key = #"ab"
  let key_bits = key_to_bitpath(key)
  let proof = Proof { root_jump: key_bits, steps: [] }
  let trie = insert(empty, key, v, proof)
  let after_pop = pop(trie, key, v, proof)
  let after_pop_max = pop_max(trie, key, v, proof)
  is_empty(after_pop) && is_empty(after_pop_max)
}

// push_min into empty → pop → empty
test prop_push_min_pop_roundtrip(v via fuzz.bytearray()) {
  let key = #"00"
  let key_bits = key_to_bitpath(key)
  let proof = Proof { root_jump: key_bits, steps: [] }
  let trie = push_min(empty, key, v, proof)
  is_empty(pop(trie, key, v, proof))
}

// push_max into empty → pop_max → empty
test prop_push_max_pop_max_roundtrip(v via fuzz.bytearray()) {
  let key = #"ff"
  let key_bits = key_to_bitpath(key)
  let proof = Proof { root_jump: key_bits, steps: [] }
  let trie = push_max(empty, key, v, proof)
  is_empty(pop_max(trie, key, v, proof))
}

// ---------------------------------------------------------------------------
// ---------------------------------------------------- Two-element properties
// ---------------------------------------------------------------------------
// Keys #"00" (min) and #"80" (max) diverge at bit 0: 0=left, 1=right.
// Two-element proof: root_jump = #"", one step consuming 8 bits.
// key_to_bitpath(#"00") = #[0,0,0,0,0,0,0,0], drop first = #[0,0,0,0,0,0,0]
// key_to_bitpath(#"80") = #[1,0,0,0,0,0,0,0], drop first = #[0,0,0,0,0,0,0]

// Pop min #"00" from {#"00", #"80"} → remaining trie has only #"80"
test prop_two_pop_min(pair via fuzz.both(fuzz.bytearray(), fuzz.bytearray())) {
  let (v1, v2) = pair
  let key_min = #"00"
  let key_max = #"80"
  let key_min_bits = key_to_bitpath(key_min)
  let key_max_bits = key_to_bitpath(key_max)
  // Build two-element trie by inserting both
  let proof_min = Proof { root_jump: key_min_bits, steps: [] }
  let proof_max_sibling =
    Indirect {
      jump: slice_bytearray(1, 7, key_min_bits),
      hash: blake2b_256(v1),
    }
  let proof_max =
    Proof {
      root_jump: #"",
      steps: [ProofStep { consumed: 8, sibling: proof_max_sibling }],
    }
  let trie =
    insert(empty, key_min, v1, proof_min)
      |> insert(key_max, v2, proof_max)
  // Pop min
  let min_sibling =
    Indirect {
      jump: slice_bytearray(1, 7, key_max_bits),
      hash: blake2b_256(v2),
    }
  let pop_proof =
    Proof {
      root_jump: #"",
      steps: [ProofStep { consumed: 8, sibling: min_sibling }],
    }
  let after = pop(trie, key_min, v1, pop_proof)
  root(after) == root_hash(key_max_bits, blake2b_256(v2))
}

// Pop max #"80" from {#"00", #"80"} → remaining trie has only #"00"
test prop_two_pop_max(pair via fuzz.both(fuzz.bytearray(), fuzz.bytearray())) {
  let (v1, v2) = pair
  let key_min = #"00"
  let key_max = #"80"
  let key_min_bits = key_to_bitpath(key_min)
  let key_max_bits = key_to_bitpath(key_max)
  // Build two-element trie by inserting both
  let proof_min = Proof { root_jump: key_min_bits, steps: [] }
  let proof_max_sibling =
    Indirect {
      jump: slice_bytearray(1, 7, key_min_bits),
      hash: blake2b_256(v1),
    }
  let proof_max =
    Proof {
      root_jump: #"",
      steps: [ProofStep { consumed: 8, sibling: proof_max_sibling }],
    }
  let trie =
    insert(empty, key_min, v1, proof_min)
      |> insert(key_max, v2, proof_max)
  // Pop max
  let max_sibling =
    Indirect {
      jump: slice_bytearray(1, 7, key_min_bits),
      hash: blake2b_256(v1),
    }
  let pop_proof =
    Proof {
      root_jump: #"",
      steps: [ProofStep { consumed: 8, sibling: max_sibling }],
    }
  let after = pop_max(trie, key_max, v2, pop_proof)
  root(after) == root_hash(key_min_bits, blake2b_256(v1))
}

// push_min #"00" into {#"80"} → root matches two-element trie
test prop_two_push_min(pair via fuzz.both(fuzz.bytearray(), fuzz.bytearray())) {
  let (v1, v2) = pair
  let key_min = #"00"
  let key_max = #"80"
  let key_max_bits = key_to_bitpath(key_max)
  let key_min_bits = key_to_bitpath(key_min)
  // Single-element trie with max only
  let single_trie = from_root(root_hash(key_max_bits, blake2b_256(v2)))
  // push_min proof: sibling is the max element
  let sibling =
    Indirect {
      jump: slice_bytearray(1, 7, key_max_bits),
      hash: blake2b_256(v2),
    }
  let proof =
    Proof { root_jump: #"", steps: [ProofStep { consumed: 8, sibling }] }
  let after = push_min(single_trie, key_min, v1, proof)
  // Build expected two-element root
  let proof_min_solo = Proof { root_jump: key_min_bits, steps: [] }
  let proof_max_sibling =
    Indirect {
      jump: slice_bytearray(1, 7, key_min_bits),
      hash: blake2b_256(v1),
    }
  let proof_max =
    Proof {
      root_jump: #"",
      steps: [ProofStep { consumed: 8, sibling: proof_max_sibling }],
    }
  let expected =
    insert(empty, key_min, v1, proof_min_solo)
      |> insert(key_max, v2, proof_max)
  root(after) == root(expected)
}

// push_max #"80" into {#"00"} → root matches two-element trie
test prop_two_push_max(pair via fuzz.both(fuzz.bytearray(), fuzz.bytearray())) {
  let (v1, v2) = pair
  let key_min = #"00"
  let key_max = #"80"
  let key_min_bits = key_to_bitpath(key_min)
  let key_max_bits = key_to_bitpath(key_max)
  // Single-element trie with min only
  let single_trie = from_root(root_hash(key_min_bits, blake2b_256(v1)))
  // push_max proof: sibling is the min element
  let sibling =
    Indirect {
      jump: slice_bytearray(1, 7, key_min_bits),
      hash: blake2b_256(v1),
    }
  let proof =
    Proof { root_jump: #"", steps: [ProofStep { consumed: 8, sibling }] }
  let after = push_max(single_trie, key_max, v2, proof)
  // Build expected two-element root
  let proof_min_solo = Proof { root_jump: key_min_bits, steps: [] }
  let proof_max_sibling =
    Indirect {
      jump: slice_bytearray(1, 7, key_min_bits),
      hash: blake2b_256(v1),
    }
  let proof_max =
    Proof {
      root_jump: #"",
      steps: [ProofStep { consumed: 8, sibling: proof_max_sibling }],
    }
  let expected =
    insert(empty, key_min, v1, proof_min_solo)
      |> insert(key_max, v2, proof_max)
  root(after) == root(expected)
}

// ---------------------------------------------------------------------------
// ------------------------------------------------- Three-element properties
// ---------------------------------------------------------------------------
// Keys: #"00", #"40", #"80"
// Bitpaths: [0,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0], [1,0,0,0,0,0,0,0]
// Tree structure:
//   Root (jump="")
//     Left (0): branch (jump="")
//       Left (0): leaf 00 (jump=[0,0,0,0,0,0])
//       Right (1): leaf 40 (jump=[0,0,0,0,0,0])
//     Right (1): leaf 80 (jump=[0,0,0,0,0,0,0])

// Pop min #"00" from {00, 40, 80} → remaining root matches {40, 80}
test prop_three_pop_min(
  triple via fuzz.both(
    fuzz.bytearray(),
    fuzz.both(fuzz.bytearray(), fuzz.bytearray()),
  ),
) {
  let (v1, (v2, v3)) = triple
  let ind_00 = Indirect { jump: #[0, 0, 0, 0, 0, 0], hash: blake2b_256(v1) }
  let ind_40 = Indirect { jump: #[0, 0, 0, 0, 0, 0], hash: blake2b_256(v2) }
  let ind_80 = Indirect { jump: #[0, 0, 0, 0, 0, 0, 0], hash: blake2b_256(v3) }
  let left_hash = combine_hash(ind_00, ind_40)
  let root_value = combine_hash(Indirect { jump: #"", hash: left_hash }, ind_80)
  let three_root = root_hash(#"", root_value)
  let trie = from_root(three_root)
  let pop_proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep { consumed: 7, sibling: ind_40 },
        ProofStep { consumed: 1, sibling: ind_80 },
      ],
    }
  let after = pop(trie, #"00", v1, pop_proof)
  let expected =
    root_hash(
      #"",
      combine_hash(
        Indirect { jump: #[1, 0, 0, 0, 0, 0, 0], hash: blake2b_256(v2) },
        ind_80,
      ),
    )
  root(after) == expected
}

// Pop max #"80" from {00, 40, 80} → remaining root matches {00, 40}
test prop_three_pop_max(
  triple via fuzz.both(
    fuzz.bytearray(),
    fuzz.both(fuzz.bytearray(), fuzz.bytearray()),
  ),
) {
  let (v1, (v2, v3)) = triple
  let ind_00 = Indirect { jump: #[0, 0, 0, 0, 0, 0], hash: blake2b_256(v1) }
  let ind_40 = Indirect { jump: #[0, 0, 0, 0, 0, 0], hash: blake2b_256(v2) }
  let ind_80 = Indirect { jump: #[0, 0, 0, 0, 0, 0, 0], hash: blake2b_256(v3) }
  let left_hash = combine_hash(ind_00, ind_40)
  let root_value = combine_hash(Indirect { jump: #"", hash: left_hash }, ind_80)
  let three_root = root_hash(#"", root_value)
  let trie = from_root(three_root)
  let left_sibling = Indirect { jump: #"", hash: left_hash }
  let pop_proof =
    Proof {
      root_jump: #"",
      steps: [ProofStep { consumed: 8, sibling: left_sibling }],
    }
  let after = pop_max(trie, #"80", v3, pop_proof)
  let expected = root_hash(#[0], combine_hash(ind_00, ind_40))
  root(after) == expected
}

// push_min #"00" into {40, 80} → root matches {00, 40, 80}
test prop_three_push_min(
  triple via fuzz.both(
    fuzz.bytearray(),
    fuzz.both(fuzz.bytearray(), fuzz.bytearray()),
  ),
) {
  let (v1, (v2, v3)) = triple
  let ind_00 = Indirect { jump: #[0, 0, 0, 0, 0, 0], hash: blake2b_256(v1) }
  let ind_40 = Indirect { jump: #[0, 0, 0, 0, 0, 0], hash: blake2b_256(v2) }
  let ind_80 = Indirect { jump: #[0, 0, 0, 0, 0, 0, 0], hash: blake2b_256(v3) }
  let two_root =
    root_hash(
      #"",
      combine_hash(
        Indirect { jump: #[1, 0, 0, 0, 0, 0, 0], hash: blake2b_256(v2) },
        ind_80,
      ),
    )
  let trie = from_root(two_root)
  let push_proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep { consumed: 7, sibling: ind_40 },
        ProofStep { consumed: 1, sibling: ind_80 },
      ],
    }
  let after = push_min(trie, #"00", v1, push_proof)
  let left_hash = combine_hash(ind_00, ind_40)
  let expected =
    root_hash(
      #"",
      combine_hash(Indirect { jump: #"", hash: left_hash }, ind_80),
    )
  root(after) == expected
}

// push_max #"80" into {00, 40} → root matches {00, 40, 80}
test prop_three_push_max(
  triple via fuzz.both(
    fuzz.bytearray(),
    fuzz.both(fuzz.bytearray(), fuzz.bytearray()),
  ),
) {
  let (v1, (v2, v3)) = triple
  let ind_00 = Indirect { jump: #[0, 0, 0, 0, 0, 0], hash: blake2b_256(v1) }
  let ind_40 = Indirect { jump: #[0, 0, 0, 0, 0, 0], hash: blake2b_256(v2) }
  let ind_80 = Indirect { jump: #[0, 0, 0, 0, 0, 0, 0], hash: blake2b_256(v3) }
  let left_hash = combine_hash(ind_00, ind_40)
  let two_root = root_hash(#[0], combine_hash(ind_00, ind_40))
  let trie = from_root(two_root)
  let left_sibling = Indirect { jump: #"", hash: left_hash }
  let push_proof =
    Proof {
      root_jump: #"",
      steps: [ProofStep { consumed: 8, sibling: left_sibling }],
    }
  let after = push_max(trie, #"80", v3, push_proof)
  let expected =
    root_hash(
      #"",
      combine_hash(Indirect { jump: #"", hash: left_hash }, ind_80),
    )
  root(after) == expected
}
