//// Bit manipulation utilities for the CSMT library.
////
//// BitPaths use a byte-per-bit representation: each byte is 0 or 1. A proof
//// carries its jumps that way, and the verifier packs each one once. It never
//// expands a key: `key_to_bitpath` and `pack_bits` are the reference the packed
//// functions are tested against, and what the tests build trees with.
////
//// The `packed_*` functions work on packed bits instead: a key kept as bytes,
//// bits in order, the most significant bit of the first byte first. They
//// return packed bit strings of `ceil(count / 8)` bytes with zero padding, whose
//// bit count the caller keeps, and equal the byte-per-bit functions above
//// composed with `pack_bits`.

use aiken/builtin.{
  and_bytearray, cons_bytearray, or_bytearray, read_bit, replicate_byte,
  shift_bytearray, slice_bytearray,
}
use aiken/primitive/bytearray

/// Expand a raw key (ByteArray) to a BitPath where each byte is one bit.
/// Each byte is expanded to 8 direction bytes, MSB first.
pub fn key_to_bitpath(key: ByteArray) -> ByteArray {
  do_expand(key, 0, bytearray.length(key), #"")
}

fn do_expand(key: ByteArray, idx: Int, len: Int, acc: ByteArray) -> ByteArray {
  if idx >= len {
    acc
  } else {
    let byte_val = bytearray.at(key, idx)
    let expanded = expand_byte(byte_val)
    do_expand(key, idx + 1, len, bytearray.concat(acc, expanded))
  }
}

fn expand_byte(b: Int) -> ByteArray {
  let b7 = b / 128
  let r7 = b % 128
  let b6 = r7 / 64
  let r6 = r7 % 64
  let b5 = r6 / 32
  let r5 = r6 % 32
  let b4 = r5 / 16
  let r4 = r5 % 16
  let b3 = r4 / 8
  let r3 = r4 % 8
  let b2 = r3 / 4
  let r2 = r3 % 4
  let b1 = r2 / 2
  let b0 = r2 % 2
  cons_bytearray(
    b7,
    cons_bytearray(
      b6,
      cons_bytearray(
        b5,
        cons_bytearray(
          b4,
          cons_bytearray(
            b3,
            cons_bytearray(b2, cons_bytearray(b1, cons_bytearray(b0, #""))),
          ),
        ),
      ),
    ),
  )
}

/// Pack a BitPath (byte-per-bit) into the wire format (8 bits per byte, MSB first).
/// Trailing bits in the last byte are zero-padded.
pub fn pack_bits(bitpath: ByteArray) -> ByteArray {
  let len = bytearray.length(bitpath)
  do_pack(bitpath, 0, len, #"")
}

fn do_pack(bp: ByteArray, pos: Int, total: Int, acc: ByteArray) -> ByteArray {
  if pos >= total {
    acc
  } else {
    let remaining = total - pos
    let n =
      if remaining >= 8 {
        8
      } else {
        remaining
      }
    let byte_val = pack_one_byte(bp, pos, n, 0, 0)
    do_pack(
      bp,
      pos + n,
      total,
      bytearray.concat(acc, cons_bytearray(byte_val, #"")),
    )
  }
}

/// Every byte of a bit path is a bit. A larger byte would carry into the bits
/// before it, and the path would pack as one with other bits.
fn pack_one_byte(bp: ByteArray, start: Int, n: Int, i: Int, acc: Int) -> Int {
  if i >= n {
    acc * pow2(8 - n)
  } else {
    let bit = bytearray.at(bp, start + i)
    expect bit <= 1
    pack_one_byte(bp, start, n, i + 1, acc * 2 + bit)
  }
}

fn pow2(n: Int) -> Int {
  when n is {
    0 -> 1
    1 -> 2
    2 -> 4
    3 -> 8
    4 -> 16
    5 -> 32
    6 -> 64
    7 -> 128
    _ -> 1
  }
}

/// Bit `index` of a packed key (0 is the most significant bit of the first
/// byte), as 0 or 1. Fails for an index before or past the key: `read_bit`
/// counts from the least significant bit of the last byte and refuses an index
/// outside the string.
pub fn packed_bit(key: ByteArray, index: Int) -> Int {
  if read_bit(key, 8 * bytearray.length(key) - 1 - index) {
    1
  } else {
    0
  }
}

/// The bits `[offset, offset + count)` of a packed key, packed: exactly
/// `ceil(count / 8)` bytes, the first bit leading, the padding bits zero. Fails
/// when the range is not inside the key.
pub fn packed_slice(key: ByteArray, offset: Int, count: Int) -> ByteArray {
  expect
    offset >= 0 && count >= 0 && offset + count <= 8 * bytearray.length(key)
  let skipped = offset % 8
  let width = ( count + 7 ) / 8
  let padding = 8 * width - count
  // The bytes that hold the range, moved left until its first bit leads, cut
  // to the width, with the bits after its last bit cleared.
  let moved =
    shift_bytearray(
      slice_bytearray(offset / 8, ( skipped + count + 7 ) / 8, key),
      skipped,
    )
  shift_bytearray(
    shift_bytearray(slice_bytearray(0, width, moved), 0 - padding),
    padding,
  )
}

/// A single bit, packed. Fails for a value that is not a bit.
pub fn packed_single(bit: Int) -> ByteArray {
  when bit is {
    0 -> #"00"
    1 -> #"80"
    _ -> fail
  }
}

/// The packed bit string `first` of `first_count` bits followed by `second` of
/// `second_count` bits, packed: `ceil((first_count + second_count) / 8)` bytes,
/// the padding bits zero. Each part must be what the functions of this module
/// return, `ceil(count / 8)` bytes with zero padding; a count that does not fit
/// its bytes fails.
pub fn packed_concat(
  first: ByteArray,
  first_count: Int,
  second: ByteArray,
  second_count: Int,
) -> ByteArray {
  expect first_count >= 0 && second_count >= 0
  expect bytearray.length(first) == ( first_count + 7 ) / 8
  expect bytearray.length(second) == ( second_count + 7 ) / 8
  let used = first_count % 8
  // The bytes from the partly used byte of `first` to the end: `second`, padded
  // with zero bytes to their number, moved right past the used bits.
  let room = ( used + second_count + 7 ) / 8
  let moved =
    shift_bytearray(
      bytearray.concat(
        second,
        replicate_byte(room - bytearray.length(second), 0),
      ),
      0 - used,
    )
  or_bytearray(
    True,
    first,
    bytearray.concat(replicate_byte(first_count / 8, 0), moved),
  )
}

/// A byte-per-bit string packed, like `pack_bits` but 64 bits per step:
/// `ceil(length / 8)` bytes, the first bit leading, the padding bits zero. Fails
/// for a byte above 1.
///
/// The string is padded with zero bytes to a multiple of 64. Three rounds of
/// shifts and ors, over the whole string, put at every byte the eight bits that
/// start there: a byte `b(i)` becomes `2 * b(i) + b(i + 1)`, that
/// `4 * .. + ..(i + 2)`, that `16 * .. + ..(i + 4)`. Only every eighth byte is
/// a packed byte. The eight of a block of 64, kept by a mask and read as a number,
/// are `p0 * 2^504 + p1 * 2^440 + .. + p7 * 2^56`; times `chunk_gather` (the sum of
/// `2^(56 * k)` for k from 0 to 7) each `p(m)` also lands at bit `504 - 8 * m`, no
/// two terms share a byte, so bits 448 to 511 of the product are `p0 .. p7`.
pub fn packed_from_bitpath(bitpath: ByteArray) -> ByteArray {
  let length = bytearray.length(bitpath)
  let high_bits = and_bytearray(False, bitpath, replicate_byte(length, 254))
  expect high_bits == replicate_byte(length, 0)
  let padded =
    bytearray.concat(bitpath, replicate_byte(( 64 - length % 64 ) % 64, 0))
  let pairs =
    or_bytearray(False, shift_bytearray(padded, 1), shift_bytearray(padded, 8))
  let quads =
    or_bytearray(False, shift_bytearray(pairs, 2), shift_bytearray(pairs, 16))
  let windows =
    or_bytearray(False, shift_bytearray(quads, 4), shift_bytearray(quads, 32))
  slice_bytearray(
    0,
    ( length + 7 ) / 8,
    pack_blocks(windows, 0, bytearray.length(padded), #""),
  )
}

const chunk_mask: ByteArray =
  #"ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000"

const chunk_gather: Int =
  0x100000000000001000000000000010000000000000100000000000001000000000000010000000000000100000000000001

const chunk_top: Int =
  0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

const word_modulus: Int = 0x10000000000000000

/// The packed bytes of the blocks of 64 bytes of `windows` from `at`, after
/// `packed`.
fn pack_blocks(
  windows: ByteArray,
  at: Int,
  total: Int,
  packed: ByteArray,
) -> ByteArray {
  if at >= total {
    packed
  } else {
    let firsts =
      and_bytearray(False, slice_bytearray(at, 64, windows), chunk_mask)
    let word =
      bytearray.to_int_big_endian(firsts) * chunk_gather / chunk_top % word_modulus
    pack_blocks(
      windows,
      at + 64,
      total,
      bytearray.concat(packed, bytearray.from_int_big_endian(word, 8)),
    )
  }
}

// ---------------------------------------------------------------
// --------------------------------------------------------- Tests
// ---------------------------------------------------------------

test key_to_bitpath_single_byte() {
  key_to_bitpath(#"a5") == #[1, 0, 1, 0, 0, 1, 0, 1]
}

test key_to_bitpath_zero() {
  key_to_bitpath(#"00") == #[0, 0, 0, 0, 0, 0, 0, 0]
}

test key_to_bitpath_ff() {
  key_to_bitpath(#"ff") == #[1, 1, 1, 1, 1, 1, 1, 1]
}

test pack_bits_roundtrip() {
  pack_bits(#[1, 0, 1, 0, 0, 1, 0, 1]) == #"a5"
}

test pack_bits_partial() {
  // 3 bits: 1,0,1 -> packed as 10100000 = 0xa0
  pack_bits(#[1, 0, 1]) == #"a0"
}

test pack_bits_empty() {
  pack_bits(#"") == #""
}

test expand_pack_roundtrip() {
  let key = #"deadbeef"
  pack_bits(key_to_bitpath(key)) == key
}
