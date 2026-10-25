//// The packed bit-path functions equal the byte-per-bit ones (test-only).
////
//// A packed key is the key itself: bits in order, most significant bit of the
//// first byte first. Every packed function is checked against its reference,
//// the key expanded by `key_to_bitpath`, cut with `slice_bytearray` and packed
//// back by `pack_bits` or `serialize_key`. Keys have 0 to 33 bytes of random or
//// repeated content; offsets and lengths cover the whole key, and the edges
//// (0, the end of the key, byte boundaries) are drawn as often as any other
//// value. A packed output has exactly ceil(bits / 8) bytes and zero padding
//// bits, and is checked for that apart from its equality with the reference.

use aiken/builtin.{blake2b_256, cons_bytearray, replicate_byte, slice_bytearray}
use aiken/collection/list
use aiken/csmt/bits.{
  key_to_bitpath, pack_bits, packed_bit, packed_concat, packed_from_bitpath,
  packed_single, packed_slice,
}
use aiken/csmt/hashing.{
  Indirect, branch_hash, combine_hash, serialize_cut_head, serialize_indirect,
  serialize_key, serialize_packed, serialize_packed_indirect, serialize_sibling,
  serialize_unjumped, unjumped_head,
}
use aiken/fuzz
use aiken/math
use aiken/primitive/bytearray

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------ Generators
// -----------------------------------------------------------------------------

/// A range of bits of a key.
type Cut {
  key: ByteArray,
  offset: Int,
  count: Int,
}

/// A part of a bit string to concatenate.
type Piece {
  Slice(Cut)
  Bit(Int)
  Jump(ByteArray)
}

/// A key of 0 to 33 bytes: random bytes, or one byte repeated (all zeros and
/// all ones among them), which lines shifted bits up with their padding.
fn keys() -> Fuzzer<ByteArray> {
  let width <- fuzz.and_then(fuzz.int_between(0, 33))
  fuzz.either(
    fuzz.bytearray_fixed(width),
    fuzz.map(
      fuzz.either(fuzz.byte(), fuzz.one_of([0, 255])),
      fn(byte) { replicate_byte(width, byte) },
    ),
  )
}

/// An integer in [0, max]: uniform, or one of the edges.
fn edge_int(max: Int) -> Fuzzer<Int> {
  fuzz.either4(
    fuzz.int_between(0, max),
    fuzz.constant(0),
    fuzz.constant(max),
    fuzz.map(fuzz.int_between(0, max / 8), fn(bytes) { bytes * 8 }),
  )
}

/// How far past an edge to go: just past it, or anywhere up to 300 bits.
fn overshoot() -> Fuzzer<Int> {
  fuzz.either(fuzz.constant(1), fuzz.int_between(1, 300))
}

/// A key and a distance past its last bit, 0 for the first bit past it.
fn key_and_past() -> Fuzzer<(ByteArray, Int)> {
  fuzz.both(keys(), fuzz.map(overshoot(), fn(past) { past - 1 }))
}

/// A range inside a key.
fn cuts() -> Fuzzer<Cut> {
  let key <- fuzz.and_then(keys())
  let total = 8 * bytearray.length(key)
  let offset <- fuzz.and_then(edge_int(total))
  let count <- fuzz.map(edge_int(total - offset))
  Cut { key, offset, count }
}

/// A byte-per-bit jump, as a proof carries it.
fn jumps(longest: Int) -> Fuzzer<ByteArray> {
  let length <- fuzz.and_then(edge_int(longest))
  fuzz.map(
    fuzz.list_between(fuzz.int_between(0, 1), length, length),
    fn(bits) {
      list.foldr(bits, #"", fn(bit, rest) { cons_bytearray(bit, rest) })
    },
  )
}

/// A byte-per-bit jump with one byte above 1 somewhere in it.
fn jumps_with_a_byte_above_one() -> Fuzzer<ByteArray> {
  let jump <- fuzz.and_then(jumps(300))
  let at <- fuzz.and_then(edge_int(bytearray.length(jump)))
  let byte <-
    fuzz.map(
      fuzz.either(
        fuzz.int_between(2, 255),
        fuzz.one_of([2, 3, 4, 8, 16, 32, 64, 128, 255]),
      ),
    )
  bytearray.concat(
    bytearray.take(jump, at),
    bytearray.push(bytearray.drop(jump, at), byte),
  )
}

fn piece_lists() -> Fuzzer<List<Piece>> {
  fuzz.list_between(
    fuzz.either3(
      fuzz.map(cuts(), Slice),
      fuzz.map(fuzz.int_between(0, 1), Bit),
      fuzz.map(jumps(70), Jump),
    ),
    1,
    4,
  )
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------------ References
// -----------------------------------------------------------------------------

/// The bits of a range of a key, one byte per bit.
fn reference_slice(key: ByteArray, offset: Int, count: Int) -> ByteArray {
  slice_bytearray(offset, count, key_to_bitpath(key))
}

fn reference_piece(piece: Piece) -> ByteArray {
  when piece is {
    Slice(Cut { key, offset, count }) -> reference_slice(key, offset, count)
    Bit(bit) -> cons_bytearray(bit, #"")
    Jump(bits) -> bits
  }
}

fn reference_concat(pieces: List<Piece>) -> ByteArray {
  list.foldl(
    pieces,
    #"",
    fn(piece, bits) { bytearray.concat(bits, reference_piece(piece)) },
  )
}

/// A piece as the packed functions build it, with its length in bits. A jump is
/// packed once, as the verifier packs a proof's jump.
fn packed_piece(piece: Piece) -> (ByteArray, Int) {
  when piece is {
    Slice(Cut { key, offset, count }) ->
      (packed_slice(key, offset, count), count)
    Bit(bit) -> (packed_single(bit), 1)
    Jump(bits) -> (packed_from_bitpath(bits), bytearray.length(bits))
  }
}

fn packed_pieces(pieces: List<Piece>) -> (ByteArray, Int) {
  list.foldl(
    pieces,
    (#"", 0),
    fn(piece, so_far) {
      let (bytes, count) = so_far
      let (next, next_count) = packed_piece(piece)
      (packed_concat(bytes, count, next, next_count), count + next_count)
    },
  )
}

/// A packed bit string of `count` bits has ceil(count / 8) bytes and zero
/// padding bits.
fn canonical(packed: ByteArray, count: Int) -> Bool {
  let width = bytearray.length(packed)
  width == ( count + 7 ) / 8 && (
    count % 8 == 0 || bytearray.at(packed, width - 1) % math.pow2(8 - count % 8) == 0
  )
}

fn bits_match(
  key: ByteArray,
  expanded: ByteArray,
  index: Int,
  total: Int,
) -> Bool {
  if index >= total {
    True
  } else {
    packed_bit(key, index) == bytearray.at(expanded, index) && bits_match(
      key,
      expanded,
      index + 1,
      total,
    )
  }
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------- Equal to the reference
// -----------------------------------------------------------------------------

test prop_every_bit_of_a_key_reads_as_in_its_expansion(key via keys()) {
  bits_match(key, key_to_bitpath(key), 0, 8 * bytearray.length(key))
}

test prop_packed_slice_equals_packed_byte_per_bit_slice(cut via cuts()) {
  let Cut { key, offset, count } = cut
  packed_slice(key, offset, count) == pack_bits(
    reference_slice(key, offset, count),
  )
}

test prop_serialized_slice_equals_serialized_byte_per_bit_slice(cut via cuts()) {
  let Cut { key, offset, count } = cut
  serialize_packed(packed_slice(key, offset, count), count) == serialize_key(
    reference_slice(key, offset, count),
  )
}

test prop_packed_concat_equals_packed_byte_per_bit_concat(
  pieces via piece_lists(),
) {
  let (packed, count) = packed_pieces(pieces)
  let reference = reference_concat(pieces)
  packed == pack_bits(reference) && count == bytearray.length(reference)
}

test prop_serialized_concat_equals_serialized_byte_per_bit_concat(
  pieces via piece_lists(),
) {
  let (packed, count) = packed_pieces(pieces)
  serialize_packed(packed, count) == serialize_key(reference_concat(pieces))
}

// Every range of each of these keys, and every pair of lengths of prefixes of two
// keys, covers the edges for certain.
test every_range_of_small_keys_equals_the_reference() {
  let keys =
    [
      #"", #"00", #"ff", #"a5", #"5a", #"c3", #"0000", #"ffff", #"a55a",
      #"deadbe",
    ]
  list.all(
    keys,
    fn(key) {
      let total = 8 * bytearray.length(key)
      list.all(
        list.range(0, total),
        fn(offset) {
          list.all(
            list.range(0, total - offset),
            fn(count) {
              let reference = reference_slice(key, offset, count)
              packed_slice(key, offset, count) == pack_bits(reference) && serialize_packed(
                packed_slice(key, offset, count),
                count,
              ) == serialize_key(reference)
            },
          )
        },
      )
    },
  )
}

test every_pair_of_prefix_lengths_concatenates_as_the_reference() {
  let left = #"a5c3"
  let right = #"5aff"
  list.all(
    list.range(0, 16),
    fn(left_count) {
      list.all(
        list.range(0, 16),
        fn(right_count) {
          let packed =
            packed_concat(
              packed_slice(left, 0, left_count),
              left_count,
              packed_slice(right, 0, right_count),
              right_count,
            )
          packed == pack_bits(
            bytearray.concat(
              reference_slice(left, 0, left_count),
              reference_slice(right, 0, right_count),
            ),
          )
        },
      )
    },
  )
}

test packed_examples() {
  packed_bit(#"a5", 0) == 1 && packed_bit(#"a5", 1) == 0 && packed_bit(#"a5", 7) == 1 && packed_bit(
    #"8001",
    8,
  ) == 0 && packed_bit(#"8001", 15) == 1 && packed_slice(#"a5", 3, 4) == #"20" && packed_slice(
    #"a5ff",
    4,
    8,
  ) == #"5f" && packed_slice(#"a5", 8, 0) == #"" && serialize_packed(
    packed_slice(#"a5", 3, 4),
    4,
  ) == #"000420" && packed_single(0) == #"00" && packed_single(1) == #"80" && packed_concat(
    #"a0",
    3,
    #"c0",
    2,
  ) == #"b8"
}

// -----------------------------------------------------------------------------
// ------------------------------------------------------------ Canonical padding
// -----------------------------------------------------------------------------

test prop_packed_slice_is_canonical(cut via cuts()) {
  let Cut { key, offset, count } = cut
  canonical(packed_slice(key, offset, count), count)
}

test prop_packed_concat_is_canonical(pieces via piece_lists()) {
  let (packed, count) = packed_pieces(pieces)
  canonical(packed, count)
}

test canonical_accepts_packed_bit_strings() {
  canonical(#"", 0) && canonical(#"a5", 8) && canonical(#"a0", 3) && canonical(
    #"a5c0",
    10,
  )
}

test canonical_rejects_a_stray_padding_bit() {
  !canonical(#"a1", 3) && !canonical(#"a5c1", 10)
}

test canonical_rejects_a_wrong_width() {
  !canonical(#"a500", 8) && !canonical(#"a5", 9) && !canonical(#"00", 0)
}

// -----------------------------------------------------------------------------
// --------------------------------------------------------------- Out of range
// -----------------------------------------------------------------------------
// A packed function refuses a position or length outside the key (a failed
// `fail` test passes only when every generated case fails).

test prop_packed_bit_refuses_an_index_before_the_key(
  at via fuzz.both(keys(), overshoot()),
) fail {
  let (key, before) = at
  packed_bit(key, 0 - before) >= 0
}

test prop_packed_bit_refuses_an_index_past_the_key(at via key_and_past()) fail {
  let (key, past) = at
  packed_bit(key, 8 * bytearray.length(key) + past) >= 0
}

test prop_packed_slice_refuses_a_negative_offset(
  cut via fuzz.both(cuts(), overshoot()),
) fail {
  let (Cut { key, count, .. }, before) = cut
  bytearray.length(packed_slice(key, 0 - before, count)) >= 0
}

test prop_packed_slice_refuses_a_negative_count(
  cut via fuzz.both(cuts(), overshoot()),
) fail {
  let (Cut { key, offset, .. }, before) = cut
  bytearray.length(packed_slice(key, offset, 0 - before)) >= 0
}

test prop_packed_slice_refuses_a_range_ending_past_the_key(
  cut via fuzz.both(cuts(), overshoot()),
) fail {
  let (Cut { key, offset, .. }, past) = cut
  let total = 8 * bytearray.length(key)
  bytearray.length(packed_slice(key, offset, total - offset + past)) >= 0
}

test prop_packed_slice_refuses_an_offset_past_the_key(
  cut via fuzz.both(cuts(), overshoot()),
) fail {
  let (Cut { key, count, .. }, past) = cut
  bytearray.length(packed_slice(key, 8 * bytearray.length(key) + past, count)) >= 0
}

test packed_single_refuses_a_value_that_is_not_a_bit() fail {
  bytearray.length(packed_single(2)) >= 0
}

test packed_single_refuses_a_negative_value() fail {
  bytearray.length(packed_single(-1)) >= 0
}

test packed_concat_refuses_a_count_that_does_not_fit_its_bytes() fail {
  bytearray.length(packed_concat(#"a5", 9, #"", 0)) >= 0
}

test packed_concat_refuses_a_second_count_that_does_not_fit_its_bytes() fail {
  bytearray.length(packed_concat(#"", 0, #"a5", 9)) >= 0
}

test packed_concat_refuses_a_negative_first_count() fail {
  bytearray.length(packed_concat(#"", -1, #"", 0)) >= 0
}

test packed_concat_refuses_a_negative_second_count() fail {
  bytearray.length(packed_concat(#"", 0, #"", -1)) >= 0
}

test serialize_packed_refuses_a_count_that_does_not_fit_its_bytes() fail {
  bytearray.length(serialize_packed(#"a5", 9)) >= 0
}

// -----------------------------------------------------------------------------
// ---------------------------------------------------------- Packing a bit path
// -----------------------------------------------------------------------------
// A jump a proof carries one byte per bit is packed once at the boundary, as
// `pack_bits` packs it, and refused as `pack_bits` refuses it.

test prop_packed_from_bitpath_equals_pack_bits(jump via jumps(300)) {
  packed_from_bitpath(jump) == pack_bits(jump)
}

test prop_packed_from_bitpath_is_canonical(jump via jumps(300)) {
  canonical(packed_from_bitpath(jump), bytearray.length(jump))
}

test prop_packed_from_bitpath_refuses_a_byte_above_one(
  jump via jumps_with_a_byte_above_one(),
) fail {
  bytearray.length(packed_from_bitpath(jump)) >= 0
}

// Every bit path of 0 to 8 bits.
test every_short_bitpath_packs_as_pack_bits() {
  list.all(
    list.range(0, 8),
    fn(length) {
      list.all(
        list.range(0, math.pow2(length) - 1),
        fn(value) {
          let bits = bits_of_value(value, length, #"")
          packed_from_bitpath(bits) == pack_bits(bits)
        },
      )
    },
  )
}

fn bits_of_value(value: Int, length: Int, acc: ByteArray) -> ByteArray {
  if length == 0 {
    acc
  } else {
    bits_of_value(value / 2, length - 1, cons_bytearray(value % 2, acc))
  }
}

test packed_from_bitpath_examples() {
  packed_from_bitpath(#[1, 0, 1, 0, 0, 1, 0, 1]) == #"a5" && packed_from_bitpath(
    #[1, 0, 1],
  ) == #"a0" && packed_from_bitpath(#"") == #"" && packed_from_bitpath(
    #[1, 1, 1, 1, 1, 1, 1, 1, 1],
  ) == #"ff80"
}

// -----------------------------------------------------------------------------
// ------------------------------------------------ Serializing for the verifier
// -----------------------------------------------------------------------------
// The verifier hashes the serialization of a node whose jump is cut from the
// packed key, or packed from a proof's jump, without a byte-per-bit string in
// between. Each serialization is checked against `serialize_indirect` of the
// byte-per-bit node, for hashes of every length a proof may carry.

/// A hash of 0 to 40 bytes: the verifier's own are 32, a proof's may be any.
fn hashes() -> Fuzzer<ByteArray> {
  fuzz.either(fuzz.bytearray_fixed(32), fuzz.bytearray_between(0, 40))
}

fn indirects() -> Fuzzer<Indirect> {
  fuzz.map2(jumps(70), hashes(), fn(jump, hash) { Indirect { jump, hash } })
}

test prop_serialized_cut_head_before_a_digest_equals_serialized_byte_per_bit_indirect(
  statement via fuzz.both(cuts(), fuzz.bytearray_fixed(32)),
) {
  let (Cut { key, offset, count }, digest) = statement
  bytearray.concat(serialize_cut_head(key, offset, count), digest) == serialize_indirect(
    Indirect { jump: reference_slice(key, offset, count), hash: digest },
  )
}

test prop_unjumped_head_before_a_digest_equals_serialized_byte_per_bit_indirect(
  digest via fuzz.bytearray_fixed(32),
) {
  bytearray.concat(unjumped_head, digest) == serialize_indirect(
    Indirect { jump: #"", hash: digest },
  )
}

test prop_serialized_packed_indirect_equals_serialized_byte_per_bit_indirect(
  statement via fuzz.both(jumps(300), hashes()),
) {
  let (jump, hash) = statement
  serialize_packed_indirect(
    packed_from_bitpath(jump),
    bytearray.length(jump),
    hash,
  ) == serialize_indirect(Indirect { jump, hash })
}

test prop_serialized_unjumped_equals_serialized_byte_per_bit_indirect(
  hash via hashes(),
) {
  serialize_unjumped(hash) == serialize_indirect(Indirect { jump: #"", hash })
}

test prop_serialized_sibling_equals_serialized_byte_per_bit_indirect(
  statement via fuzz.both(jumps(300), hashes()),
) {
  let (jump, hash) = statement
  serialize_sibling(jump, hash) == serialize_indirect(Indirect { jump, hash })
}

test prop_branch_hash_equals_combined_byte_per_bit_nodes(
  statement via fuzz.tuple3(fuzz.int_between(0, 1), indirects(), indirects()),
) {
  let (direction, mine, other) = statement
  branch_hash(direction, serialize_indirect(mine), serialize_indirect(other)) == if direction == 0 {
    combine_hash(mine, other)
  } else {
    combine_hash(other, mine)
  }
}

test prop_serialize_cut_head_refuses_a_range_past_the_key(
  cut via fuzz.both(cuts(), overshoot()),
) fail {
  let (Cut { key, offset, .. }, past) = cut
  let total = 8 * bytearray.length(key)
  bytearray.length(serialize_cut_head(key, offset, total - offset + past)) >= 0
}

test serialize_packed_indirect_refuses_a_count_that_does_not_fit_its_bytes() fail {
  bytearray.length(serialize_packed_indirect(#"a5", 9, #"")) >= 0
}

test prop_serialize_sibling_refuses_a_jump_byte_above_one(
  jump via jumps_with_a_byte_above_one(),
) fail {
  bytearray.length(serialize_sibling(jump, #"")) >= 0
}

test serialized_examples() {
  serialize_cut_head(#"a5", 3, 4) == #"0004200020" && serialize_packed_indirect(
    #"a0",
    3,
    #"",
  ) == #"0003a00000" && serialize_sibling(#[1], #"bb") == #"0001800001bb" && serialize_sibling(
    #"",
    #"bb",
  ) == #"00000001bb" && branch_hash(0, #"aa", #"0001800001bb") == blake2b_256(
    #"aa0001800001bb",
  ) && branch_hash(1, #"aa", #"0001800001bb") == blake2b_256(#"0001800001bbaa")
}

// A bit path is packed in blocks of 64 bits after three rounds of shifts over
// the whole string: the edges are at 63, 64 and 65 bits and at multiples of 64.
fn single_one(length: Int, at: Int) -> ByteArray {
  bytearray.concat(
    bytearray.concat(replicate_byte(at, 0), #[1]),
    replicate_byte(length - at - 1, 0),
  )
}

fn every_single_one_packs_as_pack_bits(length: Int) -> Bool {
  list.all(
    list.range(0, length - 1),
    fn(at) {
      let bits = single_one(length, at)
      packed_from_bitpath(bits) == pack_bits(bits)
    },
  )
}

test every_single_one_of_63_bits_packs_as_pack_bits() {
  every_single_one_packs_as_pack_bits(63)
}

test every_single_one_of_64_bits_packs_as_pack_bits() {
  every_single_one_packs_as_pack_bits(64)
}

test every_single_one_of_65_bits_packs_as_pack_bits() {
  every_single_one_packs_as_pack_bits(65)
}

test every_single_one_of_129_bits_packs_as_pack_bits() {
  every_single_one_packs_as_pack_bits(129)
}

test all_ones_pack_as_pack_bits_at_every_edge_length() {
  list.all(
    [1, 7, 8, 9, 63, 64, 65, 127, 128, 129, 192, 255, 256, 257],
    fn(length) {
      let bits = replicate_byte(length, 1)
      packed_from_bitpath(bits) == pack_bits(bits)
    },
  )
}
