// Auto-generated CSMT test vectors from haskell-mts
// Tests the Aiken CSMT against the reference Haskell.

use aiken/csmt.{
  Proof, ProofStep, delete, empty, from_root, has, insert, is_empty, root,
  update,
}
use aiken/csmt/hashing.{Indirect}

test vec_has_single() {
  let trie =
    from_root(
      #"9a45be5c807ec78e51e2676529adf0dd38cbc0a148e19a6117b4d0bc62a8b844",
    )
  let proof = Proof { root_jump: #[1, 0, 1, 0, 1, 0, 1, 1], steps: [] }
  has(trie, #"ab", #"cd", proof)
}

test vec_insert_into_empty() {
  let proof = Proof { root_jump: #[1, 0, 1, 0, 1, 0, 1, 1], steps: [] }
  let trie = insert(empty, #"ab", #"cd", proof)
  root(trie) == #"9a45be5c807ec78e51e2676529adf0dd38cbc0a148e19a6117b4d0bc62a8b844"
}

test vec_has_two_left() {
  let trie =
    from_root(
      #"11abc6871031864533c39361919fa24379b73cbeebf789a0863684101905c0c1",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 8,
          sibling: Indirect {
            jump: #[0, 0, 0, 0, 0, 0, 0],
            hash: #"4324d0dc945c746e3be93be15b636ec1684108806912a479e8a34b2858be114a",
          },
        },
      ],
    }
  has(trie, #"00", #"aa", proof)
}

test vec_has_two_right() {
  let trie =
    from_root(
      #"11abc6871031864533c39361919fa24379b73cbeebf789a0863684101905c0c1",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 8,
          sibling: Indirect {
            jump: #[0, 0, 0, 0, 0, 0, 0],
            hash: #"55951e629cad560ea5f8be280c35d8788ee84324b842fee1b41c546efb62d2d5",
          },
        },
      ],
    }
  has(trie, #"80", #"bb", proof)
}

test vec_has_shared_prefix_left() {
  let trie =
    from_root(
      #"048bc31b759974033c09d0c7d3728f9fee50afeb184da66dfe86d6041a23fd57",
    )
  let proof =
    Proof {
      root_jump: #[1, 0, 1, 0, 1, 0, 1, 1],
      steps: [
        ProofStep {
          consumed: 8,
          sibling: Indirect {
            jump: #[0, 0, 0, 0, 0, 0, 0],
            hash: #"95c3003a78585e0db8c9496f6deef4de0ff000994b8534cd66d4fe96bb21ddd3",
          },
        },
      ],
    }
  has(trie, #"ab00", #"11", proof)
}

test vec_has_shared_prefix_right() {
  let trie =
    from_root(
      #"048bc31b759974033c09d0c7d3728f9fee50afeb184da66dfe86d6041a23fd57",
    )
  let proof =
    Proof {
      root_jump: #[1, 0, 1, 0, 1, 0, 1, 1],
      steps: [
        ProofStep {
          consumed: 8,
          sibling: Indirect {
            jump: #[0, 0, 0, 0, 0, 0, 0],
            hash: #"4c54f47d69e097eed691c686ac18444a10d4abe934c311d0fffba9a3928f9e71",
          },
        },
      ],
    }
  has(trie, #"ab80", #"22", proof)
}

test vec_has_three_a() {
  let trie =
    from_root(
      #"c79caacc79c111a2b4ed0f19fe832b7d4673f2b7dd3505bbc6beb82b3be6ba0b",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 7,
          sibling: Indirect {
            jump: #[0, 0, 0, 0, 0, 0],
            hash: #"bb30a42c1e62f0afda5f0a4e8a562f7a13a24cea00ee81917b86b89e801314aa",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #[0, 0, 0, 0, 0, 0, 0],
            hash: #"e88bd757ad5b9bedf372d8d3f0cf6c962a469db61a265f6418e1ffed86da29ec",
          },
        },
      ],
    }
  has(trie, #"00", #"01", proof)
}

test vec_has_three_b() {
  let trie =
    from_root(
      #"c79caacc79c111a2b4ed0f19fe832b7d4673f2b7dd3505bbc6beb82b3be6ba0b",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 7,
          sibling: Indirect {
            jump: #[0, 0, 0, 0, 0, 0],
            hash: #"ee155ace9c40292074cb6aff8c9ccdd273c81648ff1149ef36bcea6ebb8a3e25",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #[0, 0, 0, 0, 0, 0, 0],
            hash: #"e88bd757ad5b9bedf372d8d3f0cf6c962a469db61a265f6418e1ffed86da29ec",
          },
        },
      ],
    }
  has(trie, #"40", #"02", proof)
}

test vec_has_three_c() {
  let trie =
    from_root(
      #"c79caacc79c111a2b4ed0f19fe832b7d4673f2b7dd3505bbc6beb82b3be6ba0b",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 8,
          sibling: Indirect {
            jump: #"",
            hash: #"193c331fc60a76375b176937ab774fb681f21a1192180476c4d2d9d72423b599",
          },
        },
      ],
    }
  has(trie, #"80", #"03", proof)
}

test vec_has_four_first() {
  let trie =
    from_root(
      #"1faeb5ccbeebe31365b83f192c005c3f40df7049bf676deaf027a0649937d770",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 7,
          sibling: Indirect {
            jump: #[0, 0, 0, 0, 0, 0],
            hash: #"ae85d245a3d00bfde01f59f3c4fe0b4bfae1cb37e9cf91929eadcea4985711de",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"1e6118b4ea7b1727b61a42bfd6b4ce81b2559c9e271ceeee78d0714c4ebe30dd",
          },
        },
      ],
    }
  has(trie, #"00", #"10", proof)
}

test vec_has_four_last() {
  let trie =
    from_root(
      #"1faeb5ccbeebe31365b83f192c005c3f40df7049bf676deaf027a0649937d770",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 7,
          sibling: Indirect {
            jump: #[0, 0, 0, 0, 0, 0],
            hash: #"0fd923ca5e7218c4ba3c3801c26a617ecdbfdaebb9c76ce2eca166e7855efbb8",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"d58cc2b187edc4bd03263f0602039d58055af9401677daa12a249f633f5a0504",
          },
        },
      ],
    }
  has(trie, #"c0", #"40", proof)
}

test vec_insert_first() {
  let proof = Proof { root_jump: #[0, 0, 0, 1, 0, 0, 0, 0], steps: [] }
  let trie = insert(empty, #"10", #"aa", proof)
  root(trie) == #"776f184b5e95aa8d39580b72b09afff2e4c34094bd6235e1a878623fc723e04d"
}

test vec_insert_second() {
  let proof =
    Proof {
      root_jump: #[0, 0],
      steps: [
        ProofStep {
          consumed: 6,
          sibling: Indirect {
            jump: #[1, 0, 0, 0, 0],
            hash: #"55951e629cad560ea5f8be280c35d8788ee84324b842fee1b41c546efb62d2d5",
          },
        },
      ],
    }
  let old_trie =
    from_root(
      #"776f184b5e95aa8d39580b72b09afff2e4c34094bd6235e1a878623fc723e04d",
    )
  let trie = insert(old_trie, #"20", #"bb", proof)
  root(trie) == #"b5e5debcb4ce43a54369142c7aef05fb6d499c43add0f9494bea2b65eafe6948"
}

test vec_delete_element() {
  let trie =
    from_root(
      #"38229998637c6785041ea879056874f78364900573c1ebe1056aac6636115ccc",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 8,
          sibling: Indirect {
            jump: #[1, 0, 1, 0, 0, 0, 0],
            hash: #"d31e47dec81e167dcb45996b101e0a32a71e8a082002baf8ee0a6924f04e78dd",
          },
        },
      ],
    }
  let trie2 = delete(trie, #"a0", #"ee", proof)
  root(trie2) == #"912a59061b756068b5e15176d0ea563a7ffaeacb313f0037c68da6bfe359e425"
}

test vec_delete_to_empty() {
  let trie =
    from_root(
      #"63e8a76461d8dfbecf669ce222cd96b69876a4caea4fd94a178dc0bd60e4bf2e",
    )
  let proof = Proof { root_jump: #[0, 1, 0, 0, 0, 0, 1, 0], steps: [] }
  let trie2 = delete(trie, #"42", #"ff", proof)
  is_empty(trie2)
}

test vec_update_value() {
  let trie =
    from_root(
      #"aeefbe3c2d8d2133bbd31e9cc43be95d0720b7f2f5dad7a5b04648f5584095e0",
    )
  let proof = Proof { root_jump: #[0, 1, 0, 0, 0, 0, 1, 0], steps: [] }
  let trie2 = update(trie, #"42", proof, #"0102", #"0304")
  root(trie2) == #"dae7868b410878d51fa9b1b3c7a9153824286445d6590bf0bb2df3f06b658377"
}
