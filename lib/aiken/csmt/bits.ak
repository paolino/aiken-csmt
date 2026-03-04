//// Bit manipulation utilities for the CSMT library.
////
//// BitPaths use a byte-per-bit representation: each byte is 0 or 1.
//// This makes tree operations trivial (index, slice, prepend, concat)
//// at the cost of 8x space. We only pack to the wire format for hashing.

use aiken/builtin.{cons_bytearray}
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

fn pack_one_byte(bp: ByteArray, start: Int, n: Int, i: Int, acc: Int) -> Int {
  if i >= n {
    acc * pow2(8 - n)
  } else {
    let bit = bytearray.at(bp, start + i)
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
