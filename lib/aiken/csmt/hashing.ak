//// Serialization and hashing for the CSMT library.
////
//// Matches the Haskell CSMT serialization format exactly:
//// - putKey(key) = 2-byte BE bit-count + packed bits
//// - putSizedByteString(bs) = 2-byte BE byte-count + bytes
//// - putIndirect(ind) = putKey(ind.jump) ++ putSizedByteString(ind.hash)
//// - rootHash(ind) = blake2b_256(putIndirect(ind))
//// - combineHash(l, r) = blake2b_256(putIndirect(l) ++ putIndirect(r))

use aiken/builtin.{blake2b_256}
use aiken/csmt/bits.{pack_bits, packed_from_bitpath, packed_slice}
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

/// Serialize a packed bit string of `count` bits in the Haskell putKey format:
/// 2-byte big-endian bit count + the packed bytes, which must be exactly
/// `ceil(count / 8)` of them.
pub fn serialize_packed(packed: ByteArray, count: Int) -> ByteArray {
  expect bytearray.length(packed) == ( count + 7 ) / 8
  concat(from_int_big_endian(count, 2), packed)
}

/// Serialize an Indirect whose jump is a packed bit string of `count` bits, in
/// the Haskell putIndirect format.
pub fn serialize_packed_indirect(
  packed: ByteArray,
  count: Int,
  hash: ByteArray,
) -> ByteArray {
  concat(serialize_packed(packed, count), serialize_sized_bs(hash))
}

/// The front of the serialized Indirect whose jump is the bits `[offset,
/// offset + count)` of a packed key and whose hash is a 32-byte digest: the
/// putKey of the jump and the length of the digest, everything before the
/// digest.
pub fn serialize_cut_head(key: ByteArray, offset: Int, count: Int) -> ByteArray {
  concat(
    concat(from_int_big_endian(count, 2), packed_slice(key, offset, count)),
    #"0020",
  )
}

/// The same front for an empty jump.
pub const unjumped_head: ByteArray = #"00000020"

/// Serialize an Indirect with an empty jump, in the Haskell putIndirect format.
pub fn serialize_unjumped(hash: ByteArray) -> ByteArray {
  if bytearray.length(hash) == 32 {
    concat(unjumped_head, hash)
  } else {
    concat(#"0000", serialize_sized_bs(hash))
  }
}

/// Serialize a proof's sibling: its byte-per-bit jump, packed here once, and its
/// hash.
pub fn serialize_sibling(jump: ByteArray, hash: ByteArray) -> ByteArray {
  if jump == #"" {
    serialize_unjumped(hash)
  } else {
    serialize_packed_indirect(
      packed_from_bitpath(jump),
      bytearray.length(jump),
      hash,
    )
  }
}

/// The hash of a branch whose child `mine` sits on the `direction` side (0: left,
/// 1: right) and whose other child is `theirs`, both serialized.
pub fn branch_hash(
  direction: Int,
  mine: ByteArray,
  theirs: ByteArray,
) -> ByteArray {
  if direction == 0 {
    blake2b_256(concat(mine, theirs))
  } else {
    blake2b_256(concat(theirs, mine))
  }
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
