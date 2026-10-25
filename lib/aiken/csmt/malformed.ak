//// Generators of false statements and malformed proofs (test-only).
////
//// A uniform random proof never reaches a root, so a soundness property over
//// it would pass without testing anything. Every proof here starts from an
//// honest one (the proof of a held key, of a neighbour, or of the tree with
//// the queried key inserted) and then damages any subset of its fields with
//// values from the field's whole domain.

use aiken/collection/list
use aiken/csmt.{CSMT, Proof, ProofStep, from_root}
use aiken/csmt/bits.{key_to_bitpath, pack_bits}
use aiken/csmt/hashing.{Indirect}
use aiken/csmt/reference.{
  Entries, branch_preimages, node_indirects, path_branches, proof_of,
  root_indirect, root_of, vector_trees,
}
use aiken/fuzz
use aiken/math
use aiken/primitive/bytearray

/// A claim about a tree, with the proof offered for it.
pub type Statement {
  entries: Entries,
  trie: CSMT,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
}

fn statement(
  entries: Entries,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
) -> Statement {
  Statement { entries, trie: from_root(root_of(entries)), key, value, proof }
}

// -----------------------------------------------------------------------------
// ----------------------------------------------------------------------- Trees
// -----------------------------------------------------------------------------

/// Trees of the committed haskell-mts vectors, or trees grown around a base
/// key by branching off it at chosen bit positions.
pub fn tree() -> Fuzzer<Entries> {
  fuzz.either(vector_tree(), grown_tree())
}

fn vector_tree() -> Fuzzer<Entries> {
  fuzz.map(
    fuzz.pick(vector_trees()),
    fn(picked) {
      let (_, (entries, _)) = picked
      entries
    },
  )
}

fn grown_tree() -> Fuzzer<Entries> {
  let width <- fuzz.and_then(fuzz.int_between(1, 3))
  let base <- fuzz.and_then(base_key(width))
  let branches <- fuzz.and_then(fuzz.list_between(branch_point(width), 0, 4))
  let values <- fuzz.map(fuzz.list_between(value(), 5, 5))
  let keys =
    list.unique(
      [
        base,
        ..list.map(
          branches,
          fn(branch) {
            let (at, noise) = branch
            branch_off(base, at, noise)
          },
        )
      ],
    )
  list.zip(keys, values)
}

/// Random bytes, or one byte repeated: repeated bytes give keys whose halves
/// repeat each other, which is what makes bit positions line up.
fn base_key(width: Int) -> Fuzzer<ByteArray> {
  fuzz.either(
    fuzz.bytearray_fixed(width),
    fuzz.map(fuzz.byte(), fn(byte) { repeat(byte, width) }),
  )
}

fn branch_point(width: Int) -> Fuzzer<(Int, ByteArray)> {
  fuzz.both(
    fuzz.map(
      fuzz.either(
        fuzz.int_between(0, 23),
        fuzz.map(fuzz.pick([0, 7, 8, 15, 16]), fn(picked) { picked.2nd }),
      ),
      fn(at) { at % ( 8 * width ) },
    ),
    fuzz.either(fuzz.constant(repeat(0, width)), fuzz.bytearray_fixed(width)),
  )
}

/// A key that shares the first `at` bits of `base`, differs at bit `at`, and
/// continues with the bits of `noise`.
fn branch_off(base: ByteArray, at: Int, noise: ByteArray) -> ByteArray {
  let base_bits = key_to_bitpath(base)
  let noise_bits = key_to_bitpath(noise)
  pack_bits(
    bytearray.concat(
      bytearray.concat(
        bytearray.take(base_bits, at),
        bytearray.push(#"", 1 - bytearray.at(base_bits, at)),
      ),
      bytearray.drop(noise_bits, at + 1),
    ),
  )
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------------ Keys
// -----------------------------------------------------------------------------

fn key_width(entries: Entries) -> Int {
  expect [(key, _), ..] = entries
  bytearray.length(key)
}

fn held_keys(entries: Entries) -> List<ByteArray> {
  list.map(entries, fn(entry) { entry.1st })
}

/// A key of the tree's width that the tree does not hold: a bit flipped, a byte
/// replaced, or random bytes.
fn same_length_key(entries: Entries, anchor: ByteArray) -> Fuzzer<ByteArray> {
  let width = key_width(entries)
  let parts <-
    fuzz.map(
      fuzz.tuple3(
        fuzz.int_between(0, 2),
        fuzz.int_between(0, 63),
        fuzz.bytearray_fixed(width),
      ),
    )
  let (shape, at, noise) = parts
  let candidate =
    when shape is {
      0 -> flip_bit(anchor, at)
      1 -> noise
      _ -> replace_byte(anchor, at % width, noise)
    }
  first_absent(held_keys(entries), candidate, at, 8 * width)
}

/// The first of the candidate and its successive bit flips that is not held.
/// The candidate and its flips are 8 * width + 1 different keys, more than any
/// tree here holds, so one of them is free.
fn first_absent(
  held: List<ByteArray>,
  candidate: ByteArray,
  at: Int,
  tries: Int,
) -> ByteArray {
  if !list.has(held, candidate) {
    candidate
  } else if tries <= 0 {
    fail @"no absent key"
  } else {
    first_absent(held, flip_bit(candidate, at), at + 1, tries - 1)
  }
}

/// A key longer or shorter than the tree's keys: a prefix of a held key, an
/// extension of it, a prefix with other bytes after it, or random bytes.
fn other_length_key(entries: Entries, anchor: ByteArray) -> Fuzzer<ByteArray> {
  let width = key_width(entries)
  let parts <-
    fuzz.map(
      fuzz.tuple3(
        fuzz.int_between(0, 4),
        fuzz.int_between(0, 63),
        fuzz.bytearray_between(0, 4),
      ),
    )
  let (shape, at, noise) = parts
  let candidate =
    when shape is {
      0 -> bytearray.take(anchor, at % width)
      1 -> bytearray.concat(anchor, noise)
      2 -> bytearray.concat(bytearray.take(anchor, at % width), noise)
      3 -> bytearray.take(bytearray.concat(noise, anchor), at % ( width + 4 ))
      _ -> noise
    }
  if bytearray.length(candidate) == width {
    bytearray.concat(candidate, #"01")
  } else {
    candidate
  }
}

fn flip_bit(key: ByteArray, at: Int) -> ByteArray {
  let bits = key_to_bitpath(key)
  let length = bytearray.length(bits)
  if length == 0 {
    key
  } else {
    let at = at % length
    pack_bits(
      bytearray.concat(
        bytearray.concat(
          bytearray.take(bits, at),
          bytearray.push(#"", 1 - bytearray.at(bits, at)),
        ),
        bytearray.drop(bits, at + 1),
      ),
    )
  }
}

fn replace_byte(key: ByteArray, at: Int, bytes: ByteArray) -> ByteArray {
  bytearray.concat(
    bytearray.concat(bytearray.take(key, at), bytearray.take(bytes, 1)),
    bytearray.drop(key, at + 1),
  )
}

/// The key cut or zero-padded to the tree's width.
fn fit(key: ByteArray, width: Int) -> ByteArray {
  bytearray.concat(
    bytearray.take(key, width),
    repeat(0, width - bytearray.length(key)),
  )
}

// -----------------------------------------------------------------------------
// --------------------------------------------------------------------- Values
// -----------------------------------------------------------------------------

pub fn value() -> Fuzzer<ByteArray> {
  fuzz.bytearray_between(0, 40)
}

/// A value different from `held`: one byte longer, one byte shorter, another
/// entry's value, a branch preimage, or random bytes.
fn wrong_value(held: ByteArray, entries: Entries) -> Fuzzer<ByteArray> {
  let parts <-
    fuzz.map(
      fuzz.tuple4(
        fuzz.int_between(0, 4),
        value(),
        fuzz.pick(entries),
        fuzz.int_between(0, 63),
      ),
    )
  let (shape, random, picked, at) = parts
  let (_, (_, other)) = picked
  let candidate =
    when shape is {
      0 -> bytearray.concat(held, #"00")
      1 -> bytearray.take(held, bytearray.length(held) - 1)
      2 -> other
      3 -> preimage_or(entries, at, random)
      _ -> random
    }
  if candidate == held {
    bytearray.concat(held, #"00")
  } else {
    candidate
  }
}

/// The value claimed for a key the tree does not hold: the anchor's own value
/// (so the leaf hash of an honest proof matches), another entry's, random bytes,
/// and, only when `preimages` allows it, a branch preimage of the tree.
fn claimed_value(
  entries: Entries,
  anchor_value: ByteArray,
  preimages: Bool,
) -> Fuzzer<ByteArray> {
  let parts <-
    fuzz.map(
      fuzz.tuple4(
        fuzz.int_between(0, 4),
        value(),
        fuzz.pick(entries),
        fuzz.int_between(0, 63),
      ),
    )
  let (shape, random, picked, at) = parts
  let (_, (_, other)) = picked
  let candidate =
    when shape is {
      0 -> other
      1 -> random
      2 -> preimage_or(entries, at, random)
      _ -> anchor_value
    }
  if !preimages && list.has(branch_preimages(entries), candidate) {
    bytearray.concat(candidate, #"00")
  } else {
    candidate
  }
}

fn preimage_or(entries: Entries, at: Int, otherwise: ByteArray) -> ByteArray {
  let preimages = branch_preimages(entries)
  when list.at(preimages, at % ( list.length(preimages) + 1 )) is {
    Some(preimage) -> preimage
    None -> otherwise
  }
}

// -----------------------------------------------------------------------------
// --------------------------------------------------------------------- Proofs
// -----------------------------------------------------------------------------

/// An honest proof to damage: the proof of the anchor key, the proof of the
/// queried key (cut or padded to the tree's width) in the tree with it inserted
/// under `value`, or the proof of another held key.
fn honest_base(
  entries: Entries,
  anchor: ByteArray,
  key: ByteArray,
  value: ByteArray,
) -> Fuzzer<Proof> {
  fuzz.map2(
    fuzz.pick(entries),
    fuzz.int_between(0, 3),
    fn(picked, how) {
      let (_, (other, _)) = picked
      when how is {
        0 -> proof_of(entries, anchor)
        1 -> proof_of(entries, anchor)
        2 -> {
          let fitted = fit(key, key_width(entries))
          proof_of(put(entries, fitted, value), fitted)
        }
        _ -> proof_of(entries, other)
      }
    },
  )
}

/// The entries with `key` set to `value`.
fn put(entries: Entries, key: ByteArray, value: ByteArray) -> Entries {
  if list.has(held_keys(entries), key) {
    list.map(
      entries,
      fn(entry) {
        if entry.1st == key {
          (key, value)
        } else {
          entry
        }
      },
    )
  } else {
    list.concat(entries, [(key, value)])
  }
}

/// Damage a proof of the statement about `key`. A third of the proofs are left
/// honest, so that the statement alone is false; otherwise the root jump, the
/// step list, or both are damaged by one or two successive operations, and each
/// of the first eight steps by one or two successive edits of its fields. Bytes
/// reach `bits + 8` in length, past the key's bit length, and `consumed` is any
/// integer. The bounds are for cost, because shrinking a failing case grows with
/// the number of random draws: a proof with more than eight steps is damaged in
/// its first eight only, and byte arrays are not longer than `bits + 8`.
fn damage(honest: Proof, key: ByteArray, entries: Entries) -> Fuzzer<Proof> {
  let bits = 8 * bytearray.length(key)
  fuzz.map(
    fuzz.tuple4(
      fuzz.int_between(0, 5),
      damaged_root_jump(honest.root_jump, key),
      damaged_steps(honest.steps, entries, bits),
      fuzz.list_between(step_edits(bits), 8, 8),
    ),
    fn(damage) {
      let (strength, root_jump, steps, edits) = damage
      when strength is {
        0 -> honest
        1 -> honest
        2 -> Proof { ..honest, root_jump }
        3 -> Proof { ..honest, steps: apply_edits(steps, edits) }
        _ -> Proof { root_jump, steps: apply_edits(steps, edits) }
      }
    },
  )
}

fn damaged_root_jump(honest: ByteArray, key: ByteArray) -> Fuzzer<ByteArray> {
  let key_bits = key_to_bitpath(key)
  let reach = bytearray.length(key_bits) + 8
  fuzz.map(
    fuzz.list_between(
      fuzz.tuple3(fuzz.int_between(0, 11), fuzz.int_between(0, 70), junk(reach)),
      1,
      2,
    ),
    fn(operations) {
      list.foldl(
        operations,
        honest,
        fn(operation, jump) {
          let (shape, at, noise) = operation
          let length = bytearray.length(key_bits)
          when shape is {
            4 -> bytearray.take(key_bits, at % ( length + 3 ))
            5 -> bytearray.concat(jump, noise)
            6 -> bytearray.take(jump, at % ( bytearray.length(jump) + 1 ))
            7 -> noise
            8 -> flip_byte(jump, at)
            9 -> key_bits
            10 -> bytearray.concat(key_bits, noise)
            11 -> bytearray.concat(jump, jump)
            _ -> jump
          }
        },
      )
    },
  )
}

/// Reshape the step list by one or two successive operations: cut it,
/// duplicate or repeat steps (to more steps than the key has bits), reorder
/// them, or add steps whose sibling is a real node of the tree.
fn damaged_steps(
  honest: List<ProofStep>,
  entries: Entries,
  bits: Int,
) -> Fuzzer<List<ProofStep>> {
  fuzz.map(
    fuzz.list_between(
      fuzz.tuple4(
        fuzz.int_between(0, 16),
        fuzz.int_between(0, 4),
        fuzz.int_between(0, bits + 3),
        foreign_step(entries, bits),
      ),
      1,
      2,
    ),
    fn(operations) {
      list.foldl(
        operations,
        honest,
        fn(operation, steps) {
          let (shape, at, count, extra) = operation
          when shape is {
            5 -> list.take(steps, at)
            6 -> list.drop(steps, at)
            7 ->
              when list.at(steps, at) is {
                Some(step) -> insert_at(steps, at, step)
                None -> steps
              }
            8 ->
              when list.at(steps, at) is {
                Some(step) ->
                  list.concat(
                    list.take(steps, at),
                    list.concat(
                      list.repeat(step, count),
                      list.drop(steps, at + 1),
                    ),
                  )
                None -> steps
              }
            9 -> list.concat(steps, [extra])
            10 -> [extra, ..steps]
            11 -> list.reverse(steps)
            12 -> []
            13 -> insert_at(steps, at, extra)
            14 ->
              list.concat(
                list.take(steps, at),
                [extra, ..list.drop(steps, at + 1)],
              )
            15 -> list.concat(steps, steps)
            16 -> list.concat(steps, list.repeat(extra, count))
            _ -> steps
          }
        },
      )
    },
  )
}

fn insert_at(
  steps: List<ProofStep>,
  at: Int,
  step: ProofStep,
) -> List<ProofStep> {
  list.concat(list.take(steps, at), [step, ..list.drop(steps, at)])
}

fn foreign_step(entries: Entries, bits: Int) -> Fuzzer<ProofStep> {
  fuzz.map2(
    fuzz.pick(node_indirects(entries)),
    consumed_value(bits),
    fn(picked, consumed) {
      let (_, sibling) = picked
      ProofStep { consumed, sibling }
    },
  )
}

/// Any integer, with the likely ones (around the key length) favoured.
fn consumed_value(bits: Int) -> Fuzzer<Int> {
  fuzz.either(fuzz.int_between(-10, bits + 8), fuzz.int())
}

type Edit =
  (Int, Int, ByteArray)

/// One or two edits of a single step: which field to damage, and with what.
fn step_edits(bits: Int) -> Fuzzer<List<Edit>> {
  fuzz.list_between(
    fuzz.tuple3(fuzz.int_between(0, 26), consumed_value(bits), junk(bits + 8)),
    1,
    2,
  )
}

fn apply_edits(
  steps: List<ProofStep>,
  edits: List<List<Edit>>,
) -> List<ProofStep> {
  when steps is {
    [] -> []
    [step, ..rest] ->
      when edits is {
        [] -> steps
        [step_edits, ..more] ->
          [
            list.foldl(
              step_edits,
              step,
              fn(edit, step) { edit_step(step, edit) },
            ),
            ..apply_edits(rest, more)
          ]
      }
  }
}

fn edit_step(step: ProofStep, edit: Edit) -> ProofStep {
  let (shape, number, noise) = edit
  let ProofStep { consumed, sibling } = step
  when shape is {
    0 -> ProofStep { consumed: number, sibling }
    1 -> ProofStep { consumed: consumed + 1, sibling }
    2 -> ProofStep { consumed: consumed - 1, sibling }
    3 -> ProofStep { consumed: consumed - 8, sibling }
    4 -> ProofStep { consumed: consumed + 8, sibling }
    5 -> ProofStep { consumed: 0, sibling }
    6 -> ProofStep { consumed, sibling: Indirect { ..sibling, jump: noise } }
    7 ->
      ProofStep {
        consumed,
        sibling: Indirect {
          ..sibling,
          jump: bytearray.take(sibling.jump, bytearray.length(sibling.jump) - 1),
        },
      }
    8 ->
      ProofStep {
        consumed,
        sibling: Indirect {
          ..sibling,
          jump: bytearray.concat(sibling.jump, #[0]),
        },
      }
    9 ->
      ProofStep {
        consumed,
        sibling: Indirect {
          ..sibling,
          jump: bytearray.concat(#[1], sibling.jump),
        },
      }
    10 -> ProofStep { consumed, sibling: Indirect { ..sibling, hash: noise } }
    11 ->
      ProofStep {
        consumed,
        sibling: Indirect { ..sibling, hash: bytearray.take(sibling.hash, 31) },
      }
    12 ->
      ProofStep {
        consumed,
        sibling: Indirect {
          ..sibling,
          hash: bytearray.concat(sibling.hash, #"00"),
        },
      }
    13 ->
      ProofStep {
        consumed,
        sibling: Indirect { ..sibling, jump: flip_byte(sibling.jump, number) },
      }
    14 ->
      ProofStep {
        consumed,
        sibling: Indirect {
          ..sibling,
          jump: bytearray.concat(sibling.jump, noise),
        },
      }
    15 ->
      ProofStep {
        consumed,
        sibling: Indirect {
          ..sibling,
          hash: bytearray.concat(sibling.hash, noise),
        },
      }
    16 ->
      ProofStep {
        consumed,
        sibling: Indirect {
          ..sibling,
          jump: bytearray.concat(sibling.jump, sibling.jump),
        },
      }
    _ -> step
  }
}

/// Bytes of any value, or bytes that are all 0 or 1, of any length up to
/// `longest`. The bit bytes are derived from drawn bytes: shrinking cost grows
/// with the number of draws, not with the length of the array.
fn junk(longest: Int) -> Fuzzer<ByteArray> {
  fuzz.map2(
    fuzz.bytearray_between(0, longest),
    fuzz.bool(),
    fn(bytes, bits_only) {
      if bits_only {
        bytearray.foldl(
          bytes,
          #"",
          fn(byte, acc) { bytearray.push(acc, byte % 2) },
        )
      } else {
        bytes
      }
    },
  )
}

/// The byte at `at` (modulo the length) replaced by the other bit value, or
/// by 2 when it is neither 0 nor 1.
fn flip_byte(bytes: ByteArray, at: Int) -> ByteArray {
  let length = bytearray.length(bytes)
  if length == 0 {
    bytes
  } else {
    let at = at % length
    let old = bytearray.at(bytes, at)
    bytearray.concat(
      bytearray.concat(
        bytearray.take(bytes, at),
        bytearray.push(
          #"",
          if old == 0 {
            1
          } else if old == 1 {
            0
          } else {
            2
          },
        ),
      ),
      bytearray.drop(bytes, at + 1),
    )
  }
}

fn repeat(byte: Int, times: Int) -> ByteArray {
  if times <= 0 {
    #""
  } else {
    bytearray.push(repeat(byte, times - 1), byte)
  }
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------ Statements
// -----------------------------------------------------------------------------

/// A true statement with its honest proof: the control that the verifier
/// accepts what the generators start from.
pub fn honest_statement() -> Fuzzer<Statement> {
  let entries <- fuzz.and_then(tree())
  fuzz.map(
    fuzz.pick(entries),
    fn(picked) {
      let (_, (key, value)) = picked
      statement(entries, key, value, proof_of(entries, key))
    },
  )
}

/// A held key claimed with a value other than the one it holds: a damaged honest
/// proof, or a proof cut to the root node and claimed with its preimage.
pub fn wrong_value_statement() -> Fuzzer<Statement> {
  fuzz.either(damaged_wrong_value_statement(), truncated_held_statement())
}

fn damaged_wrong_value_statement() -> Fuzzer<Statement> {
  let entries <- fuzz.and_then(tree())
  let picked <- fuzz.and_then(fuzz.pick(entries))
  let (_, (key, held)) = picked
  let wrong <- fuzz.and_then(wrong_value(held, entries))
  let honest <- fuzz.and_then(honest_base(entries, key, key, wrong))
  fuzz.map(
    damage(honest, key, entries),
    fn(proof) { statement(entries, key, wrong, proof) },
  )
}

/// A key of the tree's length that the tree does not hold, claimed with any
/// value, branch preimages included: a damaged honest proof, or a proof cut to
/// the root node and claimed with its preimage.
pub fn absent_key_statement() -> Fuzzer<Statement> {
  fuzz.either(damaged_absent_key_statement(), truncated_absent_statement())
}

fn damaged_absent_key_statement() -> Fuzzer<Statement> {
  let entries <- fuzz.and_then(tree())
  let picked <- fuzz.and_then(fuzz.pick(entries))
  let (_, (anchor, anchor_value)) = picked
  let key <- fuzz.and_then(same_length_key(entries, anchor))
  let value <- fuzz.and_then(claimed_value(entries, anchor_value, True))
  let honest <- fuzz.and_then(honest_base(entries, anchor, key, value))
  fuzz.map(
    damage(honest, key, entries),
    fn(proof) { statement(entries, key, value, proof) },
  )
}

/// A key longer or shorter than the tree's keys, claimed with any value that
/// is not a branch preimage of the tree: a damaged honest proof, or a proof
/// rebuilt to fit a shorter key.
pub fn other_length_key_statement() -> Fuzzer<Statement> {
  fuzz.either3(
    damaged_other_length_statement(),
    rebuilt_statement(),
    offered_statement(),
  )
}

/// The honest proof of a held key, undamaged, offered for a key that extends it
/// or cuts it short. Half the anchors are the smallest or the largest key, so
/// that the minimum and maximum variants, whose directions must be all 0 or all
/// 1, see a proof they would otherwise refuse before the check under test.
fn offered_statement() -> Fuzzer<Statement> {
  let entries <- fuzz.and_then(tree())
  let parts <-
    fuzz.map(
      fuzz.tuple4(
        fuzz.pick(entries),
        fuzz.int_between(0, 3),
        fuzz.bytearray_between(1, 4),
        fuzz.int_between(0, 63),
      ),
    )
  let (picked, extreme, noise, at) = parts
  let (_, (any, _)) = picked
  let keys = held_keys(entries)
  let anchor =
    when extreme is {
      0 -> extremum(keys, Less)
      1 -> extremum(keys, Greater)
      _ -> any
    }
  expect Some((_, value)) =
    list.find(entries, fn(entry) { entry.1st == anchor })
  let key =
    if at % 2 == 0 {
      bytearray.concat(anchor, noise)
    } else {
      bytearray.take(anchor, at % key_width(entries))
    }
  statement(entries, key, value, proof_of(entries, anchor))
}

fn extremum(keys: List<ByteArray>, side: Ordering) -> ByteArray {
  expect [first, ..rest] = keys
  list.foldl(
    rest,
    first,
    fn(key, best) {
      if bytearray.compare(key, best) == side {
        key
      } else {
        best
      }
    },
  )
}

fn damaged_other_length_statement() -> Fuzzer<Statement> {
  let entries <- fuzz.and_then(tree())
  let picked <- fuzz.and_then(fuzz.pick(entries))
  let (_, (anchor, anchor_value)) = picked
  let key <- fuzz.and_then(other_length_key(entries, anchor))
  let value <- fuzz.and_then(claimed_value(entries, anchor_value, False))
  let honest <- fuzz.and_then(honest_base(entries, anchor, key, value))
  fuzz.map(
    damage(honest, key, entries),
    fn(proof) { statement(entries, key, value, proof) },
  )
}

/// A statement the tree does not make true, within the amended scope: a wrong
/// value, an absent key of the tree's length, or a key of another length.
pub fn false_statement() -> Fuzzer<Statement> {
  fuzz.either4(
    wrong_value_statement(),
    absent_key_statement(),
    other_length_key_statement(),
    rebuilt_statement(),
  )
}

// -----------------------------------------------------------------------------
// ----------------------------------------------------- Proofs of a shorter key
// -----------------------------------------------------------------------------

/// A key shorter than the tree's keys can read the same hashed structure as a
/// held key when a step reads bits it has already consumed: the structure then
/// spans more key bits than the queried key has. That needs a held key whose
/// two bytes repeat, so that the bits read back are the bits the structure
/// holds (all equal bits, 00 or ff, for steps that consume nothing, and for the
/// minimum and maximum variants whose directions must all be 0 or all be 1), and
/// branches at consecutive positions (7 and 8) or a chain of them.
fn chain_tree() -> Fuzzer<Entries> {
  let repeated <-
    fuzz.and_then(
      fuzz.either3(
        fuzz.byte(),
        fuzz.map(fuzz.pick([0, 255]), fn(picked) { picked.2nd }),
        fuzz.map(fuzz.pick([0, 255]), fn(picked) { picked.2nd }),
      ),
    )
  let positions <-
    fuzz.and_then(
      fuzz.either(fuzz.constant([0, 7, 8]), fuzz.constant(list.range(0, 8))),
    )
  let values <- fuzz.map(fuzz.list_between(value(), 10, 10))
  let base = repeat(repeated, 2)
  let keys =
    [base, ..list.map(positions, fn(at) { branch_off(base, at, repeat(0, 2)) })]
  list.zip(keys, values)
}

/// The first byte of a repeated-byte key, claimed with that key's value, and
/// the honest proof of the whole key with steps that read bits again: one step
/// of a single bit consumes eight bits fewer, every such step consumes none, or
/// each step is changed by one of a few offsets.
fn rebuilt_statement() -> Fuzzer<Statement> {
  let entries <- fuzz.and_then(chain_tree())
  let mode <- fuzz.and_then(fuzz.int_between(0, 2))
  let offsets <- fuzz.map(fuzz.list_between(fuzz.int_between(0, 4), 12, 12))
  expect [(base, claimed), ..] = entries
  let honest = proof_of(entries, base)
  let steps =
    when mode is {
      0 -> shift_first_single_bit_step(honest.steps)
      1 ->
        list.map(
          honest.steps,
          fn(step) {
            if step.consumed == 1 {
              ProofStep { ..step, consumed: 0 }
            } else {
              step
            }
          },
        )
      _ -> list.map2(honest.steps, offsets, offset_step)
    }
  statement(
    entries,
    bytearray.take(base, 1),
    claimed,
    Proof { ..honest, steps },
  )
}

fn shift_first_single_bit_step(steps: List<ProofStep>) -> List<ProofStep> {
  when steps is {
    [] -> []
    [step, ..rest] ->
      if step.consumed == 1 {
        [ProofStep { ..step, consumed: -7 }, ..rest]
      } else {
        [step, ..shift_first_single_bit_step(rest)]
      }
  }
}

fn offset_step(step: ProofStep, offset: Int) -> ProofStep {
  when offset is {
    1 -> ProofStep { ..step, consumed: step.consumed - 8 }
    2 -> ProofStep { ..step, consumed: 0 }
    3 -> ProofStep { ..step, consumed: step.consumed - 1 }
    4 -> ProofStep { ..step, consumed: step.consumed + 8 }
    _ -> step
  }
}

// -----------------------------------------------------------------------------
// -------------------------------------------------- Proofs that stop at a node
// -----------------------------------------------------------------------------

/// A tree whose keys diverge only in their last one to seven bits, the last bit
/// half the time, so that the bits below the root jump are few: a proof that
/// stops at the root leaves between one and seven key bits unhashed.
fn close_tree() -> Fuzzer<Entries> {
  let width <- fuzz.and_then(fuzz.int_between(1, 3))
  let base <- fuzz.and_then(base_key(width))
  let branches <-
    fuzz.and_then(
      fuzz.list_between(
        fuzz.both(
          fuzz.map(
            fuzz.either(fuzz.constant(1), fuzz.int_between(1, 7)),
            fn(back) { 8 * width - back },
          ),
          fuzz.either(
            fuzz.constant(repeat(0, width)),
            fuzz.bytearray_fixed(width),
          ),
        ),
        1,
        3,
      ),
    )
  let values <- fuzz.map(fuzz.list_between(value(), 4, 4))
  let keys =
    list.unique(
      [
        base,
        ..list.map(
          branches,
          fn(branch) {
            let (at, noise) = branch
            branch_off(base, at, noise)
          },
        )
      ],
    )
  list.zip(keys, values)
}

/// A proof of a held key cut to its root jump, with no steps: it ends at the
/// root node, so the bits of the key below the root jump are never hashed, and
/// the value that hashes to that node is its preimage, the serialized pair of
/// its children.
fn root_only(entries: Entries, anchor: ByteArray) -> Proof {
  Proof { ..proof_of(entries, anchor), steps: [] }
}

/// A held key claimed with the preimage of the root node and a proof that stops
/// there, on a tree of any kind or one whose keys diverge in their last bits.
fn truncated_held_statement() -> Fuzzer<Statement> {
  let entries <- fuzz.and_then(fuzz.either(tree(), close_tree()))
  let picked <- fuzz.map(fuzz.pick(entries))
  let (_, (key, held)) = picked
  let wrong = preimage_or(entries, 0, bytearray.concat(held, #"00"))
  statement(
    entries,
    key,
    if wrong == held {
      bytearray.concat(held, #"00")
    } else {
      wrong
    },
    root_only(entries, key),
  )
}

/// A key of the tree's length that shares the root jump of a held key and
/// differs below it, claimed with the preimage of the root node and a proof that
/// stops there.
fn truncated_absent_statement() -> Fuzzer<Statement> {
  let entries <- fuzz.and_then(fuzz.either(tree(), close_tree()))
  let picked <- fuzz.and_then(fuzz.pick(entries))
  let (_, (anchor, anchor_value)) = picked
  let at <- fuzz.map(fuzz.int_between(0, 63))
  let proof = root_only(entries, anchor)
  let below = 8 * key_width(entries) - bytearray.length(proof.root_jump)
  let key =
    first_absent(
      held_keys(entries),
      flip_bit(
        anchor,
        bytearray.length(proof.root_jump) + at % math.max(below, 1),
      ),
      at,
      8 * key_width(entries),
    )
  statement(entries, key, preimage_or(entries, 0, anchor_value), proof)
}

// -----------------------------------------------------------------------------
// --------------------------------------------------------------- Held-key proofs
// -----------------------------------------------------------------------------
/// A held key offered to `miss`, `insert`, `push_min` and `push_max`, which claim
/// it absent, with a proof built to make that claim verify. Half the keys are
/// the smallest or the largest key, so that the minimum and maximum variants,
/// whose directions must be all 0 or all 1, see proofs they would otherwise
/// refuse before the check under test.
pub fn held_key_statement() -> Fuzzer<Statement> {
  let entries <- fuzz.and_then(fuzz.either(tree(), close_tree()))
  let parts <-
    fuzz.and_then(
      fuzz.tuple3(fuzz.pick(entries), fuzz.int_between(0, 3), value()),
    )
  let (picked, extreme, claimed) = parts
  let (_, (any, _)) = picked
  let keys = held_keys(entries)
  let key =
    when extreme is {
      0 -> extremum(keys, Less)
      1 -> extremum(keys, Greater)
      _ -> any
    }
  held_statement(entries, key, claimed)
}

/// The smallest key of a tree, offered as absent.
pub fn held_minimum_statement() -> Fuzzer<Statement> {
  extreme_statement(Less)
}

/// The largest key of a tree, offered as absent.
pub fn held_maximum_statement() -> Fuzzer<Statement> {
  extreme_statement(Greater)
}

fn extreme_statement(side: Ordering) -> Fuzzer<Statement> {
  let entries <- fuzz.and_then(fuzz.either(tree(), extreme_tree(side)))
  let claimed <- fuzz.and_then(value())
  held_statement(entries, extremum(held_keys(entries), side), claimed)
}

/// A tree whose smallest (or largest) key is a random key of the tree, and whose
/// other keys all leave it at a bit where it holds 0 (or 1): that key then goes
/// the same way at every branch of its path, with random bits between them.
fn extreme_tree(side: Ordering) -> Fuzzer<Entries> {
  let width <- fuzz.and_then(fuzz.int_between(1, 3))
  let key <- fuzz.and_then(fuzz.bytearray_fixed(width))
  let branches <- fuzz.and_then(fuzz.list_between(branch_point(width), 1, 3))
  let values <- fuzz.map(fuzz.list_between(value(), 4, 4))
  let direction =
    if side == Less {
      0
    } else {
      1
    }
  let key_bits = key_to_bitpath(key)
  let positions =
    list.filter(
      list.range(0, bytearray.length(key_bits) - 1),
      fn(at) { bytearray.at(key_bits, at) == direction },
    )
  let others =
    when positions is {
      [] -> []
      _ ->
        list.map(
          branches,
          fn(branch) {
            let (at, noise) = branch
            expect Some(position) =
              list.at(positions, at % list.length(positions))
            branch_off(key, position, noise)
          },
        )
    }
  list.zip(list.unique([key, ..others]), values)
}

fn held_statement(
  entries: Entries,
  key: ByteArray,
  claimed: ByteArray,
) -> Fuzzer<Statement> {
  fuzz.map(
    held_key_proof(entries, key),
    fn(proof) { statement(entries, key, claimed, proof) },
  )
}

/// A damaged honest proof, a proof that absorbs a node (one and a half in four),
/// one that absorbs a node and is then damaged, or one whose lowest sibling
/// carries into the bit the verifier prepends.
fn held_key_proof(entries: Entries, key: ByteArray) -> Fuzzer<Proof> {
  fuzz.either4(
    {
      let honest <- fuzz.and_then(neighbour_base(entries, key))
      damage(honest, key, entries)
    },
    absorbing_proof(entries, key),
    fuzz.either(
      absorbing_proof(entries, key),
      {
        let forged <- fuzz.and_then(absorbing_proof(entries, key))
        damage(forged, key, entries)
      },
    ),
    carrying_proof(entries, key),
  )
}

/// The jump bytes of the lowest sibling are not bits: the byte `2^by + bit` at
/// index `by - 1` adds `2^by` to the packed value, which flips the bit `by`
/// places before it. The node it stands for is the one at `level` of the path,
/// or the top node, and the removed branch reads a position that holds 1, so
/// that the bit the verifier prepends is 0 where the node has 1 and the carry
/// puts it right.
fn carrying_proof(entries: Entries, key: ByteArray) -> Fuzzer<Proof> {
  fuzz.map(
    fuzz.tuple4(
      fuzz.int_between(0, 15),
      fuzz.int_between(0, 63),
      fuzz.either(fuzz.constant(1), fuzz.int_between(1, 7)),
      fuzz.int_between(0, 8),
    ),
    fn(params) {
      let (which, draw, by, cut) = params
      let top = root_indirect(entries)
      let path = path_branches(entries, key)
      let key_bits = key_to_bitpath(key)
      let level = which % ( list.length(path) + 1 ) - 1
      if level < 0 {
        let kept = cut % ( bytearray.length(top.jump) + 1 )
        let read = reading_after(bytearray.drop(key_bits, kept), 1, 0, draw)
        carrying(absorbing(entries, key, level, kept, read, read + 1, 0), by)
      } else {
        let position = branch_position(path, level)
        let read =
          reading_after(
            bytearray.drop(key_bits, bytearray.length(top.jump)),
            1,
            position + 1,
            draw,
          )
        carrying(
          absorbing(entries, key, level, 0, read, read - position, 0),
          by,
        )
      }
    },
  )
}

/// The proof with `2^by` added to the byte at index `by - 1` of the jump of its
/// lowest sibling.
pub fn carrying(proof: Proof, by: Int) -> Proof {
  when proof.steps is {
    [] -> proof
    [bottom, ..rest] -> {
      let jump = bottom.sibling.jump
      let at = by - 1
      let carried =
        if at < bytearray.length(jump) {
          bytearray.concat(
            bytearray.concat(
              bytearray.take(jump, at),
              bytearray.push(#"", bytearray.at(jump, at) + math.pow(2, by)),
            ),
            bytearray.drop(jump, at + 1),
          )
        } else {
          jump
        }
      Proof {
        ..proof,
        steps: [
          ProofStep {
            ..bottom,
            sibling: Indirect { ..bottom.sibling, jump: carried },
          },
          ..rest
        ],
      }
    }
  }
}

/// The honest proof of the held key, of another held key, of the held key in the
/// tree with a neighbour of it added (a deeper path), or in the tree with
/// another key removed (a shallower one).
fn neighbour_base(entries: Entries, key: ByteArray) -> Fuzzer<Proof> {
  fuzz.map(
    fuzz.tuple4(
      fuzz.pick(entries),
      fuzz.int_between(0, 3),
      fuzz.int_between(0, 63),
      fuzz.bytearray_fixed(key_width(entries)),
    ),
    fn(parts) {
      let (picked, how, at, noise) = parts
      let (_, (other, _)) = picked
      when how is {
        0 -> proof_of(entries, key)
        1 -> proof_of(entries, other)
        2 ->
          proof_of(
            put(
              entries,
              branch_off(key, at % ( 8 * key_width(entries) ), noise),
              #"",
            ),
            key,
          )
        _ ->
          proof_of(
            list.filter(
              entries,
              fn(entry) { entry.1st != other || other == key },
            ),
            key,
          )
      }
    },
  )
}

/// Proofs that absorb a node of the tree on the held key's path (see
/// `absorbing`): half of them restore the node exactly, the others also vary how
/// many bits are dropped, how many key bits the steps consume, and the root jump.
fn absorbing_proof(entries: Entries, key: ByteArray) -> Fuzzer<Proof> {
  fuzz.either(
    exact_absorbing_proof(entries, key),
    loose_absorbing_proof(entries, key),
  )
}

/// The removed branch reads a position that holds the opposite of the node's
/// first bit, so that the bit the verifier prepends restores the node.
fn exact_absorbing_proof(entries: Entries, key: ByteArray) -> Fuzzer<Proof> {
  fuzz.map2(
    fuzz.int_between(0, 15),
    fuzz.int_between(0, 63),
    fn(which, draw) {
      let level = which % ( list.length(path_branches(entries, key)) + 1 ) - 1
      absorbing(
        entries,
        key,
        level,
        0,
        read_position(entries, key, level, 0, draw, True),
        1,
        0,
      )
    },
  )
}

/// Which node, how many bits it drops, and how many key bits the two lowest
/// steps consume are drawn from small ranges around the values an honest proof
/// has, zero and negative consumed included. Half the time the position is
/// chosen as in the exact proofs.
fn loose_absorbing_proof(entries: Entries, key: ByteArray) -> Fuzzer<Proof> {
  fuzz.map(
    fuzz.tuple7(
      fuzz.int_between(0, 15),
      fuzz.either(fuzz.int_between(-3, 3), fuzz.int_between(-8, 12)),
      fuzz.int_between(0, 7),
      fuzz.int_between(0, 7),
      fuzz.int_between(0, 8),
      fuzz.int_between(0, 9),
      fuzz.bool(),
    ),
    fn(params) {
      let (which, middle, dropped, off_by, cut, cursor, aware) = params
      let top = root_indirect(entries)
      let path = path_branches(entries, key)
      let level = which % ( list.length(path) + 1 ) - 1
      let kept =
        if level < 0 {
          cut % ( bytearray.length(top.jump) + 1 )
        } else {
          0
        }
      let base =
        if level < 0 {
          cursor
        } else {
          branch_position(path, level) + middle
        }
      let drop_count =
        if dropped == 0 {
          0
        } else if dropped == 7 {
          2
        } else {
          1
        }
      let shift =
        if off_by == 6 {
          1
        } else if off_by == 7 {
          -1
        } else {
          0
        }
      absorbing(
        entries,
        key,
        level,
        kept,
        read_position(entries, key, level, kept, base, aware),
        drop_count,
        shift,
      )
    },
  )
}

/// The position, counted after the root jump (cut to `kept` bits at the top
/// node), that the removed branch reads: `base`, or when `restoring`, the one
/// among the positions holding the opposite of the absorbed node's first bit that
/// `base` points to.
fn read_position(
  entries: Entries,
  key: ByteArray,
  level: Int,
  kept: Int,
  base: Int,
  restoring: Bool,
) -> Int {
  if restoring {
    let top = root_indirect(entries)
    let key_bits = key_to_bitpath(key)
    if level < 0 {
      reading(
        bytearray.drop(key_bits, kept),
        1 - first_bit(bytearray.drop(top.jump, kept)),
        base,
      )
    } else {
      expect Some((child, _)) = list.at(path_branches(entries, key), level)
      reading(
        bytearray.drop(key_bits, bytearray.length(top.jump)),
        1 - first_bit(child.jump),
        base,
      )
    }
  } else {
    base
  }
}

/// The proof of `key` in which the sibling of the bottom step is the node of the
/// tree at `level` on the key's path (the top node when `level` is -1), with
/// `drop_count` of its first jump bits dropped, so that the bit the verifier
/// prepends when it collapses the branch gives that node back. The bottom step
/// reads the key bit at `read` (counted after the root jump) and consumes the
/// bits from there to the end of the key, plus `shift`. At a level of the path
/// the next step is the honest sibling of that level, consuming the bits
/// between its branch and `read`, and the steps above it are honest. At the top
/// node the root jump is cut to `kept` bits and there is no other step.
pub fn absorbing(
  entries: Entries,
  key: ByteArray,
  level: Int,
  kept: Int,
  read: Int,
  drop_count: Int,
  shift: Int,
) -> Proof {
  let top = root_indirect(entries)
  let bits = 8 * bytearray.length(key)
  if level < 0 {
    Proof {
      root_jump: bytearray.take(top.jump, kept),
      steps: [
        ProofStep {
          consumed: bits - kept - read + shift,
          sibling: Indirect {
            jump: bytearray.drop(top.jump, kept + drop_count),
            hash: top.hash,
          },
        },
      ],
    }
  } else {
    let path = path_branches(entries, key)
    expect Some((child, sibling)) = list.at(path, level)
    let above = list.take(path, level)
    let position = branch_position(path, level)
    Proof {
      root_jump: top.jump,
      steps: [
        ProofStep {
          consumed: bits - bytearray.length(top.jump) - read + shift,
          sibling: Indirect {
            jump: bytearray.drop(child.jump, drop_count),
            hash: child.hash,
          },
        },
        ProofStep { consumed: read - position, sibling },
        ..list.reverse(
          list.map(
            above,
            fn(branch) {
              ProofStep {
                consumed: 1 + bytearray.length(branch.1st.jump),
                sibling: branch.2nd,
              }
            },
          ),
        )
      ],
    }
  }
}

/// The position of the branch bit at `level` of the path, counted after the root
/// jump.
fn branch_position(path: List<(Indirect, Indirect)>, level: Int) -> Int {
  list.foldl(
    list.take(path, level),
    0,
    fn(branch, at) { at + 1 + bytearray.length(branch.1st.jump) },
  )
}

fn first_bit(bits: ByteArray) -> Int {
  if bytearray.length(bits) == 0 {
    0
  } else {
    bytearray.at(bits, 0)
  }
}

/// The position among the positions of `bits` that hold `wanted` which `draw`
/// points to, or `draw` itself when there is none.
fn reading(bits: ByteArray, wanted: Int, draw: Int) -> Int {
  let positions =
    list.filter(
      list.range(0, bytearray.length(bits) - 1),
      fn(at) { bytearray.at(bits, at) == wanted },
    )
  when list.at(positions, math.abs(draw) % ( list.length(positions) + 1 )) is {
    Some(at) -> at
    None -> draw
  }
}

/// Like `reading`, among the positions from `from` on.
fn reading_after(bits: ByteArray, wanted: Int, from: Int, draw: Int) -> Int {
  let positions =
    list.filter(
      list.range(from, bytearray.length(bits) - 1),
      fn(at) { bytearray.at(bits, at) == wanted },
    )
  when list.at(positions, math.abs(draw) % ( list.length(positions) + 1 )) is {
    Some(at) -> at
    None -> draw
  }
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------ Honest insertions
// -----------------------------------------------------------------------------

/// A key about to be added to a tree, with the proof of its absence that the
/// reference trie builds (the proof of the key in the tree that holds it), and
/// the root hash of the tree after the addition.
pub type Insertion {
  before: CSMT,
  after: ByteArray,
  key: ByteArray,
  value: ByteArray,
  proof: Proof,
}

fn insertion(entries: Entries, key: ByteArray) -> Insertion {
  expect Some((_, value)) = list.find(entries, fn(entry) { entry.1st == key })
  Insertion {
    before: from_root(
      root_of(list.filter(entries, fn(entry) { entry.1st != key })),
    ),
    after: root_of(entries),
    key,
    value,
    proof: proof_of(entries, key),
  }
}

/// Any key of a tree, taken out of it, or any key of the tree's length that the
/// tree does not hold, added to it.
pub fn honest_insertion() -> Fuzzer<Insertion> {
  fuzz.either(taken_out_insertion(), absent_key_insertion())
}

fn taken_out_insertion() -> Fuzzer<Insertion> {
  let entries <- fuzz.and_then(fuzz.either(tree(), close_tree()))
  fuzz.map(
    fuzz.pick(entries),
    fn(picked) {
      let (_, (key, _)) = picked
      insertion(entries, key)
    },
  )
}

fn absent_key_insertion() -> Fuzzer<Insertion> {
  let entries <- fuzz.and_then(fuzz.either(tree(), close_tree()))
  let picked <- fuzz.and_then(fuzz.pick(entries))
  let (_, (anchor, _)) = picked
  let key <- fuzz.and_then(same_length_key(entries, anchor))
  fuzz.map(value(), fn(value) { insertion(put(entries, key, value), key) })
}

/// The smallest key of a tree, taken out of it.
pub fn honest_minimum_insertion() -> Fuzzer<Insertion> {
  fuzz.map(
    fuzz.either(tree(), close_tree()),
    fn(entries) { insertion(entries, extremum(held_keys(entries), Less)) },
  )
}

/// The largest key of a tree, taken out of it.
pub fn honest_maximum_insertion() -> Fuzzer<Insertion> {
  fuzz.map(
    fuzz.either(tree(), close_tree()),
    fn(entries) { insertion(entries, extremum(held_keys(entries), Greater)) },
  )
}

/// A key of a tree of at least two keys that is not its smallest, taken out of it.
pub fn non_minimum_insertion() -> Fuzzer<Insertion> {
  not_extreme_insertion(Less)
}

/// A key of a tree of at least two keys that is not its largest, taken out of it.
pub fn non_maximum_insertion() -> Fuzzer<Insertion> {
  not_extreme_insertion(Greater)
}

fn not_extreme_insertion(side: Ordering) -> Fuzzer<Insertion> {
  let entries <-
    fuzz.and_then(
      fuzz.such_that(
        fuzz.either3(tree(), close_tree(), crooked_tree(side)),
        fn(entries) { list.length(entries) >= 2 },
      ),
    )
  fuzz.map(
    fuzz.pick(entries),
    fn(picked) {
      let (_, (any, _)) = picked
      let keys = held_keys(entries)
      insertion(
        entries,
        if any == extremum(keys, side) {
          extremum(
            keys,
            if side == Less {
              Greater
            } else {
              Less
            },
          )
        } else {
          any
        },
      )
    },
  )
}

/// A tree with a key that takes the way an extremum does at every branch but
/// the root, where it takes the other way, so that only the top of its path
/// betrays it: below the root it shares a branch with keys that leave it at a
/// few later bits.
fn crooked_tree(side: Ordering) -> Fuzzer<Entries> {
  let width <- fuzz.and_then(fuzz.int_between(1, 3))
  let flips <-
    fuzz.and_then(fuzz.list_between(fuzz.int_between(2, 8 * width - 1), 2, 3))
  let values <- fuzz.map(fuzz.list_between(value(), 6, 6))
  let right =
    if side == Less {
      0
    } else {
      1
    }
  let key =
    pack_bits(
      bytearray.concat(
        bytearray.push(#"", 1 - right),
        repeat(right, 8 * width - 1),
      ),
    )
  let straight = pack_bits(repeat(right, 8 * width))
  let others = list.map(flips, fn(at) { branch_off(key, at, repeat(0, width)) })
  list.zip(list.unique([key, straight, ..others]), values)
}
