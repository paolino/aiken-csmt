// Measurement test vectors

use aiken/csmt.{Proof, ProofStep, from_root, has, insert, miss, root}
use aiken/csmt/hashing.{Indirect}

test measure_has_1() {
  let trie =
    from_root(
      #"647e28c5f234613a832a28600c9b85d184abffca5b46a19985314d6ded585cae",
    )
  let proof =
    Proof {
      root_jump: #"00000100010001000100000000010100010001000101000101000001000101010001010001000101010101010001010101000101000000010001010101000001000101000100010001000101010000010001010001010101010001010100010100000101000001000000000101000101000101010100010001010101010000010001010001010001000000000101000000010101010000010100000001000101010100010000000101000000010001000100000000010000010001000001010000000001000001010101000101000101000101000100010001010101010101000100010000010000000100000101000000000100010000010100010100000001",
      steps: [],
    }
  has(
    trie,
    #"2a86ad976bf7b1796ab96fbb321b7af96d0c798bd18a84a613db6afea44c29b1",
    #"67ba1862ce8fb4a49555aceafd30388b27a243951d3db55826cd4868086aa0d8",
    proof,
  )
}

test measure_miss_1() {
  let trie =
    from_root(
      #"647e28c5f234613a832a28600c9b85d184abffca5b46a19985314d6ded585cae",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 256,
          sibling: Indirect {
            jump: #"000100010001000100000000010100010001000101000101000001000101010001010001000101010101010001010101000101000000010001010101000001000101000100010001000101010000010001010001010101010001010100010100000101000001000000000101000101000101010100010001010101010000010001010001010001000000000101000000010101010000010100000001000101010100010000000101000000010001000100000000010000010001000001010000000001000001010101000101000101000101000100010001010101010101000100010000010000000100000101000000000100010000010100010100000001",
            hash: #"6a0eb36a27d1dcb1825712b29a7441f77c319f501c13346352d563dc5c86c7c4",
          },
        },
      ],
    }
  miss(
    trie,
    #"a753e4aabc24ba2022f35e3909da54529fa7a1c57e4808f27157ce56a66ce457",
    proof,
  )
}

test measure_insert_1() {
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 256,
          sibling: Indirect {
            jump: #"000100010001000100000000010100010001000101000101000001000101010001010001000101010101010001010101000101000000010001010101000001000101000100010001000101010000010001010001010101010001010100010100000101000001000000000101000101000101010100010001010101010000010001010001010001000000000101000000010101010000010100000001000101010100010000000101000000010001000100000000010000010001000001010000000001000001010101000101000101000101000100010001010101010101000100010000010000000100000101000000000100010000010100010100000001",
            hash: #"6a0eb36a27d1dcb1825712b29a7441f77c319f501c13346352d563dc5c86c7c4",
          },
        },
      ],
    }
  let old_trie =
    from_root(
      #"647e28c5f234613a832a28600c9b85d184abffca5b46a19985314d6ded585cae",
    )
  let trie =
    insert(
      old_trie,
      #"a753e4aabc24ba2022f35e3909da54529fa7a1c57e4808f27157ce56a66ce457",
      #"cf8fb465416171af275f075ddf135eea7380d998cf77e2d971f4eb70a3f144ff",
      proof,
    )
  root(trie) == #"dce639bad7f0746a8c84eb4db0dbdeadb1b6f182ec371f1f6385303256fc92a8"
}

test measure_has_10() {
  let trie =
    from_root(
      #"c5c301ea71235fd302c3be4b7ce95ce0c3a35b3a99fa9163576c1a1a5e4767cf",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 252,
          sibling: Indirect {
            jump: #"0000000001000000000000000000010000000001000101000101010000000101000000010100010100000101000000000000010101010101010101000100000000010100010100010000000000010001000100000000010101000100010000000000000100000101000100000100010001010100000000000001010001000001010100000000010001000001010000000000010001010100000000010101010100000100010100010001010101010001000101010101010000010101010001000001000100010100000000000100010001010000000000010001000100010101000000000100010101010000000001000000000000000001000000",
            hash: #"a4b5e642f1e08c64fdf76f3302c0d32fde3820cb461362c779cb337d0b1817a6",
          },
        },
        ProofStep {
          consumed: 2,
          sibling: Indirect {
            jump: #"00000001000100000001010101000000010000000001010101010100000000000100000101010100010101010101000100000100000001010001010100000100010100010001010000010001000001010000010100010100000001000100010101010000000000010100010000010000010101010100010001010100010000010001010101010101000101010100000001010100000000010000010001010100010001010001010100000000010001010001000000000100000000000001000100000100010000000101010001010100010001010000000101000101000100010100010101000101010001000000000000000101010001000100000000",
            hash: #"a9722ac987866dccab3ccca11afbcfadf601d535513e9d4de16837e0d305d144",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"923ef68cbcc5118336d7ffa6ca85f5a5583fdc139363f22ea83da7a24af80e64",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"00",
            hash: #"33a3647473e2aed763cd228a297407ad7acded46378668c0fd89deb5cb44bc5a",
          },
        },
      ],
    }
  has(
    trie,
    #"126cb74f2b80003dfa39c1a5362bf18b07399db394cc9f3d1e45c3f6319d5b2d",
    #"eea2131d1e79263b40f56190fd209c77791ba0e379846084824302175ef32af4",
    proof,
  )
}

test measure_miss_10() {
  let trie =
    from_root(
      #"c5c301ea71235fd302c3be4b7ce95ce0c3a35b3a99fa9163576c1a1a5e4767cf",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 255,
          sibling: Indirect {
            jump: #"",
            hash: #"33a3647473e2aed763cd228a297407ad7acded46378668c0fd89deb5cb44bc5a",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"c90c744573001f3970bdd93c6657f0345c923cefe1e3ae672c621f239764c633",
          },
        },
      ],
    }
  miss(
    trie,
    #"e3d632062ce5fe4cb10887d437ac4a7156ccb4ea5d84a15e12181462630875a8",
    proof,
  )
}

test measure_insert_10() {
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 255,
          sibling: Indirect {
            jump: #"",
            hash: #"33a3647473e2aed763cd228a297407ad7acded46378668c0fd89deb5cb44bc5a",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"c90c744573001f3970bdd93c6657f0345c923cefe1e3ae672c621f239764c633",
          },
        },
      ],
    }
  let old_trie =
    from_root(
      #"c5c301ea71235fd302c3be4b7ce95ce0c3a35b3a99fa9163576c1a1a5e4767cf",
    )
  let trie =
    insert(
      old_trie,
      #"e3d632062ce5fe4cb10887d437ac4a7156ccb4ea5d84a15e12181462630875a8",
      #"ff12a843b9231e0187544b6139a36b19f6f970334265a1588aac78d32b9f89e1",
      proof,
    )
  root(trie) == #"affd11221554ed61088c9f568c12ead78900d2aab626906c1efc4dab125dda6e"
}

test measure_has_1000() {
  let trie =
    from_root(
      #"c768a8fec689b438001d888f771a523d9bced49a7fbf6af751a41d974372d9fc",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 245,
          sibling: Indirect {
            jump: #"00000000010101000001000101010101010101000001010000010101010001000001000001000100010101010100000000010101000000000100000001010001010001010100000000010000000101010100000101000001000101010000000100010101010101010100000100010100010000010001000001000001000101000100010000010100010000010100000101010001000100010000000100000000000100000001010000000100010001000101000001010100000001010000010000000100000000000000010000010100010001010101000100010100010101010100000100010001000100000100000000000101",
            hash: #"965e0efae9bbeb4338400c0ff4c52b0dc058f993738bdb1db5ce4578397e210e",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"0000010101000000010101000000000101000000010001010000010101010000000001000100010100000001010100010100010001000000000101000101010001010101010100000000010101010100010101010001000101010001010101010000000001010000000000010100010101010101000100000001000100010001000001010001010100010100000001000001000000010100010000000101010100010000010000010001000001000000010001010101010001010101010101010100010001010001010001010101000100010101010100010101010101010001010000000000010001010000010100010001010001",
            hash: #"1facf1ef84bda1a31f71399dfe975df2f56c8b43589375b3615f1e11cc890118",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"010100000000000100000001010000010001010100010101000000000101000101010001000000010101010000010000000000000000010100000000010000000001000001000000010101000100010000010000000101000001000001010100010101010101010000000000010001010000000101010101010100010100010001000001010000000001000100010000000100000001000000010001010101000000010000000100000100000100010000000001010100010101000001000001010000010000010101000000010100010101000000000000010001000100010001000001000001000001010001000001000101000100",
            hash: #"16e256dcd41c8ea1fa6a2bcacb7316e9c30279dee09f4938519079e85985cefc",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"e5d8141f2810938cb55406561bcc8d8ed304951f17e155b99652bf46d83413f3",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"c3102146a88daa64f977f4821680f6cb271b2acd13e816d38a0eade10e46d035",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"7aa5716524e001d70db4f488fd56bc4963460538595fece2e61a5a30118268ec",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"72e2cd592b81b3132f6725e8394649ad2e404bb772b94f1e3da9b968ea2eca3f",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"00e4ae16841e8431232bdb7c8503f70c1104a53b88cfda3a1bcbd055763cdb5c",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"cf22bec27be94295a29df6ceebdfde5a013d87e887a12cb62ea700467dd72baf",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"42b25aa11996de9530e4f3d5eef282331c9a92fc04fd3fce1d1d73a8cb25a251",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"59700d682f809ba6b7fa9e54b5e80510b2654639e3155604498845111bba9fec",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"fd39f42ba3ffc21b6b24df1a9c0bf8b961217870aa52b6bbbef3a0728546d402",
          },
        },
      ],
    }
  has(
    trie,
    #"e4b9d73509da18c6be3a2297cdbe3946ae786a5316715bcadd4a167d4aedabfe",
    #"9a86fb0ca488cecee12405d90fe456070a67d85d6ce353097b99c47853f8346c",
    proof,
  )
}

test measure_miss_1000() {
  let trie =
    from_root(
      #"c768a8fec689b438001d888f771a523d9bced49a7fbf6af751a41d974372d9fc",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 245,
          sibling: Indirect {
            jump: #"01000001010101000101010101000000000001000101010101000000000101010101000000010000010101010000000100000101010000000100000100000000000000000000010101000100010100010100010101000001010101010100000100010001010000010101010001010001010000010001000100010001010101010100010000010101010001010100000001000000000000010001000001010001000101000001010000010000010001000100000000010001000100010000000000000100000100000000010001010000000101000100000100010000010001000101010100010001000101000101000101010001",
            hash: #"8fd6533f7eccfb3e87da28d24f0e2c8d98450ef7d3182c01e761b7cff4741824",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"0000010001000100010001010100000101000101010000010101010000000000010001010000010000010100000100000000010000000000010101000101000101000101000100010101010100000001010101010001000000000000000001000100010100000001010001000000000000010000000001010000000100010100000000010000000000000001000101010000000100000000010100000001000101010100010001010000010101010100010000010100010001000101000100010101010001010001010101010000000000000101000101000101000000000001010101000100010000010101000001000101000100",
            hash: #"6855636c0b774ae8eca47fb291fc22fd5b04b0f492adb6e858c824f02bf15907",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"010100010001000001010100000001010101010100010101010000000001010000010101010100000101000100010101010001010101000100010100010000000001010100010001000000010001010001000100010000010100010000010001010001010001000101000101010001000100000100010000000000010001010100000001010000000100000001000001000001010100000000000101010101010101010000010001010000000100000100010101000001000101000100010100000000010100000100010000000000000100000000000001010000010100010101010001000000000000010101000001010101010101",
            hash: #"00e298cadd6dfbbe594ff320b6e3aaee440dc89fa544d573faa7d13e532e9d80",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"2755f96ceacdf15bf2c485c86a65695a111d7a35b0cd4ae3ed557cc0bdfd2260",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"adbba3c5b273ab57c8ba24480c240ed042b37b3649cc6be9eff82b432d644980",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"9b9c1e6b8597c7df7c938fa22f9b3588a3972ab5fae5546a999fd7e30fe84fca",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"a3e3f495961175639ae6c0978aac0ec8e1e30a68b89541dc0868517fef11c038",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"f0fceec3eaa6625c3b2ce9a3e315a6ec4cb92a61075781b97fc8efdb4917620d",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"bfd98fd5242cb2fe5062a32d7f1331190698e54cd793287189c2202e927d5be6",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"a3f11a0da5ec8cca2d1d78ae9f3d64cecb75e5d90ca76a9551578e7c3135f30c",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"59700d682f809ba6b7fa9e54b5e80510b2654639e3155604498845111bba9fec",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"fd39f42ba3ffc21b6b24df1a9c0bf8b961217870aa52b6bbbef3a0728546d402",
          },
        },
      ],
    }
  miss(
    trie,
    #"d2a17b09ee0b5d2499a302bd6025139f87fa210b0ff395570fcca503142bfb41",
    proof,
  )
}

test measure_insert_1000() {
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 245,
          sibling: Indirect {
            jump: #"01000001010101000101010101000000000001000101010101000000000101010101000000010000010101010000000100000101010000000100000100000000000000000000010101000100010100010100010101000001010101010100000100010001010000010101010001010001010000010001000100010001010101010100010000010101010001010100000001000000000000010001000001010001000101000001010000010000010001000100000000010001000100010000000000000100000100000000010001010000000101000100000100010000010001000101010100010001000101000101000101010001",
            hash: #"8fd6533f7eccfb3e87da28d24f0e2c8d98450ef7d3182c01e761b7cff4741824",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"0000010001000100010001010100000101000101010000010101010000000000010001010000010000010100000100000000010000000000010101000101000101000101000100010101010100000001010101010001000000000000000001000100010100000001010001000000000000010000000001010000000100010100000000010000000000000001000101010000000100000000010100000001000101010100010001010000010101010100010000010100010001000101000100010101010001010001010101010000000000000101000101000101000000000001010101000100010000010101000001000101000100",
            hash: #"6855636c0b774ae8eca47fb291fc22fd5b04b0f492adb6e858c824f02bf15907",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"010100010001000001010100000001010101010100010101010000000001010000010101010100000101000100010101010001010101000100010100010000000001010100010001000000010001010001000100010000010100010000010001010001010001000101000101010001000100000100010000000000010001010100000001010000000100000001000001000001010100000000000101010101010101010000010001010000000100000100010101000001000101000100010100000000010100000100010000000000000100000000000001010000010100010101010001000000000000010101000001010101010101",
            hash: #"00e298cadd6dfbbe594ff320b6e3aaee440dc89fa544d573faa7d13e532e9d80",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"2755f96ceacdf15bf2c485c86a65695a111d7a35b0cd4ae3ed557cc0bdfd2260",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"adbba3c5b273ab57c8ba24480c240ed042b37b3649cc6be9eff82b432d644980",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"9b9c1e6b8597c7df7c938fa22f9b3588a3972ab5fae5546a999fd7e30fe84fca",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"a3e3f495961175639ae6c0978aac0ec8e1e30a68b89541dc0868517fef11c038",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"f0fceec3eaa6625c3b2ce9a3e315a6ec4cb92a61075781b97fc8efdb4917620d",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"bfd98fd5242cb2fe5062a32d7f1331190698e54cd793287189c2202e927d5be6",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"a3f11a0da5ec8cca2d1d78ae9f3d64cecb75e5d90ca76a9551578e7c3135f30c",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"59700d682f809ba6b7fa9e54b5e80510b2654639e3155604498845111bba9fec",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"fd39f42ba3ffc21b6b24df1a9c0bf8b961217870aa52b6bbbef3a0728546d402",
          },
        },
      ],
    }
  let old_trie =
    from_root(
      #"c768a8fec689b438001d888f771a523d9bced49a7fbf6af751a41d974372d9fc",
    )
  let trie =
    insert(
      old_trie,
      #"d2a17b09ee0b5d2499a302bd6025139f87fa210b0ff395570fcca503142bfb41",
      #"33750cb2fe36a06d1cc782f11252c3bc215a27fca73f22e03ccda704063401d8",
      proof,
    )
  root(trie) == #"1a005233b5351e339e19abef109353ae586e3abda6407fdae0ad2bfccfb7eed3"
}

test measure_has_100000() {
  let trie =
    from_root(
      #"c451f6d4cde6b7ed2e6a5376599176244c315eb5bf1d44736ef3d73e5bae7f58",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 238,
          sibling: Indirect {
            jump: #"010000010000000000010001010100000001010100010001010000010000010100010000010100000001000001000000010000000100000001010101010001010000010000000101000101000101010100010001010000000001000000000001010100000000010000010101010001000000000101000100000101000100000000010100000001000100010001000001000001010001000000000100000100000001000101000001000100000101000000000001000001010100000100000001000100000100010100010100000001010001010001010000010001010100000000000101010101000000000101",
            hash: #"ac5446f48416e9bb777bf864dc036f37d44d3f49ceda339c17abb7f26ef4a783",
          },
        },
        ProofStep {
          consumed: 2,
          sibling: Indirect {
            jump: #"",
            hash: #"7c7e09dd91142c997e14b9307fe45494e1d552b481ac667f8204fbfcb27ab84e",
          },
        },
        ProofStep {
          consumed: 2,
          sibling: Indirect {
            jump: #"00010000000001000100010000000101010001000100010100010101010000010101000100000100000101010100010101010100000100000101000100000101010101000100010100010001010001000101010000010000010101010100000101000100000000000101010101000001000001010001000000010100000101000101000101000100000001000100010001000101000100000001000001000100010000010000000000010100000001000001010101000001000101010100000100000001000001000100000001010001010100000000010100010101010100000001010101000101010001010101010001",
            hash: #"75d03698d360028863b3660c8f1e1fc110869b7c0b81fd04b35f1c8de0a698e8",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"9f8b047f9eba05a5fca9a5a2952436bbb2eb8adefa39596caa62f8d848290c6e",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"69568ed2786060fd621fb744d822fe56c67e10322e395e7680145b5b6887ddad",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"fd257c7cf294285c05215e0a8e9350079dbedd605c90c80234d045920113b9d8",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"b3b6785ee90402a50a27fff29640c4fe88c0115ac8bc2e93c30e53cda1310f1a",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"e79a1154d3a45f5976483fb0db018caf02b9556b62e79ad9f7b06ac967655f31",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"20b08f73eb124f39c28eea5936723351ecad22150ae3cf4980e5c2e200df6c0c",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"f4ef07a6589f729367db239d6fe9333da71b1df0de06e1943c75cc076152ca89",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"010cf1b2d2e68ec34d4b21d998d0d1b44913b49f111c250884befba7a4eb1c87",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"fd0787e2805fca07013d010de56e6faab231e9b64510e9747b1adbc6512e02b4",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"609900ec52c7cf2de99e526faf5f01258e9b0f497af049c86426bbe1e6625b38",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"204f4dfb498f3f77203b1e405cc9f53bce130dd29fdb2a812e36f6622d2c569e",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"0885a00981858a2375dddc806a62685aef8013374d70949bfcbaa26e77274166",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"d0a021b22de176ed877edc6896b0a455f804b14cc7b2098bc76222cac2040b9e",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"69edfd5cc3d645961385feb7aadd4cc186d58d63d5ff3f39991260e45d78346f",
          },
        },
      ],
    }
  has(
    trie,
    #"42c4479911ecdb65f63f330d29cd4e23149100895680f2e7cf3b47c247da9956",
    #"d9f037d75845b079fefe451de0b5c381663ff64c38e7ea44500d14751feffb10",
    proof,
  )
}

test measure_miss_100000() {
  let trie =
    from_root(
      #"c451f6d4cde6b7ed2e6a5376599176244c315eb5bf1d44736ef3d73e5bae7f58",
    )
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 239,
          sibling: Indirect {
            jump: #"01000001000000010100000100010000000100000001000101010100000000010100000101000101000101010001010100010000000001000100010001010100010000010101010101000101010000000001010000000100010001000101000100010000000101010100000100010001010101010001000100000000000101010101010100000000000101010101010000000101010100000100000001010101000001010000000001010001010100010000000001000000000100000101010101000101010101000101010000010000000101000100000001000101000100010001000101000000010100000001",
            hash: #"d02a3f8d1c3ec2e9fe6bb6596d9c475c3659c57e04828babb419582746ccbdad",
          },
        },
        ProofStep {
          consumed: 3,
          sibling: Indirect {
            jump: #"",
            hash: #"457f8cb40cac4d2484b0732f543f0ac667ac99abc562e0d67575281c5f54099f",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"eba388c957243eca7eb66174888e2005971773d0848e3659b1fa2600ad418613",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"f0f97a5ab29f32015082e17fc2b6dec30a8e67be07d05f1a273aa037fcc660f8",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"fac08c00e81de6d08f464ec7143b1cb3df59c5eb6900b973be7531645dcb411c",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"c9c0986ce6ad04c9005e1791a36e260b63e2c1e99b7abda62c3c7714c961c5e5",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"2ed325e1e07e22c4709385d4910c531150fbf7e0c3c72d9df1d4744e4294c1af",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"58bf08f6d3ec97ae05080df0d9db561a5ed0746be68eb8ac8a1c3508417e5b5f",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"cfa8a5e8ac3dd7f77de3369e4795244ea15fd291ea056401d3ea86164589e129",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"bc9ca2ab25859de71cfff5c9c9675c1bbf0fe66aabcbb255b922831230004fa1",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"274aab437eb5c4bdfc71d2bb84143f5485f13984d84cf71a0da772bc7977de4f",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"5dca42967c9694c839dfb02369b8bd74ff17b6e33a959e153663120e846b1f7e",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"408f97ce654b61dd5893c6057ed641e62ca4386ab103351828996723ee3d6807",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"da271f819a62178c46fba20e26098cedc88f4fba71bc9a8e3f39cdb2591d583c",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"e45775cd085eae3c86c560c2ec5993f21c2c2acbd636943ef071bf7cc3bbbd1c",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"69edfd5cc3d645961385feb7aadd4cc186d58d63d5ff3f39991260e45d78346f",
          },
        },
      ],
    }
  miss(
    trie,
    #"3b97e871ba36b473ecb0b63abb74cc2dec727768a572d70297bb5427d1a0fd09",
    proof,
  )
}

test measure_insert_100000() {
  let proof =
    Proof {
      root_jump: #"",
      steps: [
        ProofStep {
          consumed: 239,
          sibling: Indirect {
            jump: #"01000001000000010100000100010000000100000001000101010100000000010100000101000101000101010001010100010000000001000100010001010100010000010101010101000101010000000001010000000100010001000101000100010000000101010100000100010001010101010001000100000000000101010101010100000000000101010101010000000101010100000100000001010101000001010000000001010001010100010000000001000000000100000101010101000101010101000101010000010000000101000100000001000101000100010001000101000000010100000001",
            hash: #"d02a3f8d1c3ec2e9fe6bb6596d9c475c3659c57e04828babb419582746ccbdad",
          },
        },
        ProofStep {
          consumed: 3,
          sibling: Indirect {
            jump: #"",
            hash: #"457f8cb40cac4d2484b0732f543f0ac667ac99abc562e0d67575281c5f54099f",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"eba388c957243eca7eb66174888e2005971773d0848e3659b1fa2600ad418613",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"f0f97a5ab29f32015082e17fc2b6dec30a8e67be07d05f1a273aa037fcc660f8",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"fac08c00e81de6d08f464ec7143b1cb3df59c5eb6900b973be7531645dcb411c",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"c9c0986ce6ad04c9005e1791a36e260b63e2c1e99b7abda62c3c7714c961c5e5",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"2ed325e1e07e22c4709385d4910c531150fbf7e0c3c72d9df1d4744e4294c1af",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"58bf08f6d3ec97ae05080df0d9db561a5ed0746be68eb8ac8a1c3508417e5b5f",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"cfa8a5e8ac3dd7f77de3369e4795244ea15fd291ea056401d3ea86164589e129",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"bc9ca2ab25859de71cfff5c9c9675c1bbf0fe66aabcbb255b922831230004fa1",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"274aab437eb5c4bdfc71d2bb84143f5485f13984d84cf71a0da772bc7977de4f",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"5dca42967c9694c839dfb02369b8bd74ff17b6e33a959e153663120e846b1f7e",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"408f97ce654b61dd5893c6057ed641e62ca4386ab103351828996723ee3d6807",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"da271f819a62178c46fba20e26098cedc88f4fba71bc9a8e3f39cdb2591d583c",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"e45775cd085eae3c86c560c2ec5993f21c2c2acbd636943ef071bf7cc3bbbd1c",
          },
        },
        ProofStep {
          consumed: 1,
          sibling: Indirect {
            jump: #"",
            hash: #"69edfd5cc3d645961385feb7aadd4cc186d58d63d5ff3f39991260e45d78346f",
          },
        },
      ],
    }
  let old_trie =
    from_root(
      #"c451f6d4cde6b7ed2e6a5376599176244c315eb5bf1d44736ef3d73e5bae7f58",
    )
  let trie =
    insert(
      old_trie,
      #"3b97e871ba36b473ecb0b63abb74cc2dec727768a572d70297bb5427d1a0fd09",
      #"da34ad35539322182a01f35a146831b03ba66f4148c4945d3cabd67c99dafbc0",
      proof,
    )
  root(trie) == #"c0c124a7669c77bb8dd9828c35926a37ef92fbdfd7d900a18106c4705fa78c79"
}
