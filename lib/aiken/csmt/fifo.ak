//// FIFO queue operations on top of a CSMT.
////
//// A FIFO is a pair of counters (head, tail) backed by a CSMT.  Keys are
//// big-endian encodings of counter values with a fixed byte-width, so trie
//// ordering matches enqueue order.
////
//// - `push`: insert at `tail`, return new state with `tail + 1`
//// - `pop`:  delete at `head`, return new state with `head + 1`
////
//// These are pure verification functions — no UTxO or transaction logic.
//// Application validators import them and add their own authorization,
//// value management, and lifecycle rules.

use aiken/csmt.{CSMT, Proof, delete, insert, root}
use aiken/primitive/bytearray.{from_int_big_endian}

/// State of a FIFO queue.
pub type Fifo {
  /// The backing CSMT.
  trie: CSMT,
  /// Index of the next element to dequeue (front).
  head: Int,
  /// Index of the next element to enqueue (back).
  tail: Int,
}

/// Enqueue a value.  Inserts at `tail` and increments it.
///
/// #### Fails when
///
/// - The proof is invalid.
/// - The key at `tail` already exists in the trie.
pub fn push(
  self: Fifo,
  index_bytes: Int,
  value: ByteArray,
  proof: Proof,
) -> Fifo {
  let key = from_int_big_endian(self.tail, index_bytes)
  let new_trie = insert(self.trie, key, value, proof)
  Fifo { trie: new_trie, head: self.head, tail: self.tail + 1 }
}

/// Dequeue a value.  Deletes at `head` and increments it.
///
/// #### Fails when
///
/// - The queue is empty (`head >= tail`).
/// - The proof is invalid.
/// - The key at `head` doesn't exist with the given value.
pub fn pop(self: Fifo, index_bytes: Int, value: ByteArray, proof: Proof) -> Fifo {
  expect self.head < self.tail
  let key = from_int_big_endian(self.head, index_bytes)
  let new_trie = delete(self.trie, key, value, proof)
  Fifo { trie: new_trie, head: self.head + 1, tail: self.tail }
}

/// Get the root hash of the backing CSMT.
pub fn root_hash(self: Fifo) -> ByteArray {
  root(self.trie)
}

/// Check whether the queue is empty.
pub fn is_empty(self: Fifo) -> Bool {
  self.head >= self.tail
}

/// Number of elements in the queue.
pub fn length(self: Fifo) -> Int {
  self.tail - self.head
}
