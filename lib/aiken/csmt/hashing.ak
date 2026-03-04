//// Serialization and hashing for the CSMT library.
////
//// Matches the Haskell CSMT serialization format exactly:
//// - putKey(key) = 2-byte BE bit-count + packed bits
//// - putSizedByteString(bs) = 2-byte BE byte-count + bytes
//// - putIndirect(ind) = putKey(ind.jump) ++ putSizedByteString(ind.hash)
//// - rootHash(ind) = blake2b_256(putIndirect(ind))
//// - combineHash(l, r) = blake2b_256(putIndirect(l) ++ putIndirect(r))

use aiken/builtin.{blake2b_256}
use aiken/csmt/bits.{pack_bits}
use aiken/primitive/bytearray.{concat, from_int_big_endian}

/// An indirect reference: a jump path (as BitPath) plus a 32-byte hash.
pub type Indirect {
  jump: ByteArray,
  hash: ByteArray,
}

/// Serialize a BitPath (byte-per-bit) in the Haskell putKey format:
/// 2-byte big-endian bit count + packed bytes.
pub fn serialize_key(bitpath: ByteArray) -> ByteArray {
  let len = bytearray.length(bitpath)
  let len_bytes = from_int_big_endian(len, 2)
  let packed = pack_bits(bitpath)
  concat(len_bytes, packed)
}

/// Serialize a ByteArray in the Haskell putSizedByteString format:
/// 2-byte big-endian byte count + bytes.
fn serialize_sized_bs(bs: ByteArray) -> ByteArray {
  let len = bytearray.length(bs)
  let len_bytes = from_int_big_endian(len, 2)
  concat(len_bytes, bs)
}

/// Serialize an Indirect in the Haskell putIndirect format:
/// putKey(jump) ++ putSizedByteString(hash).
pub fn serialize_indirect(ind: Indirect) -> ByteArray {
  concat(serialize_key(ind.jump), serialize_sized_bs(ind.hash))
}

/// Compute rootHash: blake2b_256(putIndirect(Indirect { jump, value })).
/// This is the hash of a single node (leaf or collapsed branch).
pub fn root_hash(jump: ByteArray, value: ByteArray) -> ByteArray {
  blake2b_256(serialize_indirect(Indirect { jump, hash: value }))
}

/// Compute combineHash: blake2b_256(putIndirect(left) ++ putIndirect(right)).
/// This is the hash of a branch node with two children.
pub fn combine_hash(left: Indirect, right: Indirect) -> ByteArray {
  blake2b_256(concat(serialize_indirect(left), serialize_indirect(right)))
}

/// Combine two indirects with direction determining order.
/// L (0): me is the left child, other is right.
/// R (1): me is the right child, other is left.
pub fn add_with_direction(
  direction: Int,
  me: Indirect,
  other: Indirect,
) -> ByteArray {
  if direction == 0 {
    combine_hash(me, other)
  } else {
    combine_hash(other, me)
  }
}

/// The null hash: 32 zero bytes, representing an empty tree.
pub const null_hash =
  #"0000000000000000000000000000000000000000000000000000000000000000"

// ---------------------------------------------------------------
// --------------------------------------------------------- Tests
// ---------------------------------------------------------------

test serialize_key_empty() {
  // Empty key: 2 zero bytes (length 0), no packed data
  serialize_key(#"") == #"0000"
}

test serialize_key_one_bit() {
  // 1 bit (value 1): length = 0x0001, packed = 0x80
  serialize_key(#[1]) == #"000180"
}

test serialize_key_eight_bits() {
  // 8 bits [1,0,1,0,0,1,0,1]: length = 0x0008, packed = 0xa5
  serialize_key(#[1, 0, 1, 0, 0, 1, 0, 1]) == #"0008a5"
}
