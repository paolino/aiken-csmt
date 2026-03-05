// Auto-generated FIFO test vectors from haskell-mts
// Tests the Aiken CSMT FIFO against the reference Haskell.

use aiken/csmt.{Proof, ProofStep, empty, from_root}
use aiken/csmt/fifo.{Fifo, is_empty, pop, push, root_hash}
use aiken/csmt/hashing.{Indirect}

test vec_fifo_push_one() {
  let fifo = Fifo { trie: empty, head: 0, tail: 0 }
  let proof = Proof { root_jump: #[0, 0, 0, 0, 0, 0, 0, 0], steps: [] }
  let fifo2 = push(fifo, 1, #"aa", proof)
  root_hash(fifo2) == #"4ec799b000855432de3e3292057fec1688f983d084747ec87b14953fdaafda98"
}

test vec_fifo_push_two() {
  let fifo =
    Fifo {
      trie: from_root(
        #"4ec799b000855432de3e3292057fec1688f983d084747ec87b14953fdaafda98",
      ),
      head: 0,
      tail: 1,
    }
  let proof =
    Proof {
      root_jump: #[0, 0, 0, 0, 0, 0, 0],
      steps: [
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"55951e629cad560ea5f8be280c35d8788ee84324b842fee1b41c546efb62d2d5",
          },
        },
      ],
    }
  let fifo2 = push(fifo, 1, #"bb", proof)
  root_hash(fifo2) == #"67cf7839c557c20a964b060669606ef1fbb184f52012a2fcbae9efa5279647fc"
}

test vec_fifo_push_three() {
  let fifo =
    Fifo {
      trie: from_root(
        #"67cf7839c557c20a964b060669606ef1fbb184f52012a2fcbae9efa5279647fc",
      ),
      head: 0,
      tail: 2,
    }
  let proof =
    Proof {
      root_jump: #[0, 0, 0, 0, 0, 0],
      steps: [
        ProofStep {
          consumed: 2,
          sibling: Indirect {
            jump: #"",
            hash: #"2b1737b2008c39d5475911ee055151b5f37252d155488d460b0f0a8ae6a54b96",
          },
        },
      ],
    }
  let fifo2 = push(fifo, 1, #"cc", proof)
  root_hash(fifo2) == #"dc84cba44c13817970e7ed159f357d0a89712a593f99e9ad9f74694f0f42932d"
}

test vec_fifo_pop_one() {
  let fifo =
    Fifo {
      trie: from_root(
        #"dc84cba44c13817970e7ed159f357d0a89712a593f99e9ad9f74694f0f42932d",
      ),
      head: 0,
      tail: 3,
    }
  let proof =
    Proof {
      root_jump: #[0, 0, 0, 0, 0, 0],
      steps: [
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"4324d0dc945c746e3be93be15b636ec1684108806912a479e8a34b2858be114a",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #[0],
            hash: #"e3f0d5af2a41c8fd042a6ec5fef8acfd591903cbb97a3ab666f08e7c39c8a948",
          },
        },
      ],
    }
  let fifo2 = pop(fifo, 1, #"aa", proof)
  root_hash(fifo2) == #"05f3ed1057820fe50b74bed41b604a1fe6569b5ba9c29db741c7bb1bfbd1c912"
}

test vec_fifo_pop_all() {
  let fifo =
    Fifo {
      trie: from_root(
        #"dc84cba44c13817970e7ed159f357d0a89712a593f99e9ad9f74694f0f42932d",
      ),
      head: 0,
      tail: 3,
    }
  let proof =
    Proof {
      root_jump: #[0, 0, 0, 0, 0, 0],
      steps: [
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"4324d0dc945c746e3be93be15b636ec1684108806912a479e8a34b2858be114a",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #[0],
            hash: #"e3f0d5af2a41c8fd042a6ec5fef8acfd591903cbb97a3ab666f08e7c39c8a948",
          },
        },
      ],
    }
  let fifo2 = pop(fifo, 1, #"aa", proof)
  let proof2 =
    Proof {
      root_jump: #[0, 0, 0, 0, 0, 0],
      steps: [
        ProofStep {
          consumed: 2,
          sibling: Indirect {
            jump: #[0],
            hash: #"e3f0d5af2a41c8fd042a6ec5fef8acfd591903cbb97a3ab666f08e7c39c8a948",
          },
        },
      ],
    }
  let fifo3 = pop(fifo2, 1, #"bb", proof2)
  let proof3 = Proof { root_jump: #[0, 0, 0, 0, 0, 0, 1, 0], steps: [] }
  let fifo4 = pop(fifo3, 1, #"cc", proof3)
  is_empty(fifo4)
}
