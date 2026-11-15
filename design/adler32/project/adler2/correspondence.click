import "../adler32-spec-u64.click";
import click::integer;

// Widen the Rust result into the LP64 C return type without losing bits.
theorem adler_result_widen(word: uint32) {
 ensures to_integer(word as uint64) == to_integer(word) by {
  have 0 <= to_integer(word);
  have to_integer(word) <= 4294967295;
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(word) => 0 <= to_integer(word);
   premise 1: to_integer(word) <= 4294967295 => to_integer(word) <= 4294967295;
   integer_cast_identity bounds [0, 1] => to_integer(word as uint64) == to_integer(word);
   conclusion 0;
  }
 }
}

// Instantiate the result premises with the independently checked C and Rust
// contracts. The arrays are their entry retained_states, not their live buffers.
theorem adler_c_rust_results(c_bytes: uint8[], rust_bytes: uint8[], length: uint64, initial_a: Integer, initial_b: Integer, c_result: uint64, rust_result: uint32) {
 requires 0 <= initial_a;
 requires initial_a <= 65520;
 requires 0 <= initial_b;
 requires initial_b <= 65520;
 requires forall (k: uint64) { k < length implies c_bytes[k] == rust_bytes[k] };
 requires to_integer(c_result) == adler_spec_checksum_u64(c_bytes, length, initial_a, initial_b);
 requires to_integer(rust_result) == adler_spec_checksum_u64(rust_bytes, length, initial_a, initial_b);
 ensures c_result == rust_result as uint64 by {
  apply(adler_spec_extensional_u64(c_bytes, rust_bytes, length, initial_a, initial_b));
  have adler_spec_checksum_u64(c_bytes, length, initial_a, initial_b) == adler_spec_checksum_u64(rust_bytes, length, initial_a, initial_b) by {
   unfold(adler_spec_checksum_u64(c_bytes, length, initial_a, initial_b));
   unfold(adler_spec_checksum_u64(rust_bytes, length, initial_a, initial_b));
   rewrite(adler_spec_a_u64(c_bytes, length, initial_a), adler_spec_a_u64(rust_bytes, length, initial_a));
   rewrite(adler_spec_b_u64(c_bytes, length, initial_a, initial_b), adler_spec_b_u64(rust_bytes, length, initial_a, initial_b));
   normalize();
  }
  apply(adler_result_widen(rust_result));
  have to_integer(c_result) == to_integer(rust_result as uint64) by solve() using {
   to_integer(c_result) == adler_spec_checksum_u64(c_bytes, length, initial_a, initial_b);
   to_integer(rust_result) == adler_spec_checksum_u64(rust_bytes, length, initial_a, initial_b);
   adler_spec_checksum_u64(c_bytes, length, initial_a, initial_b) == adler_spec_checksum_u64(rust_bytes, length, initial_a, initial_b);
   to_integer(rust_result as uint64) == to_integer(rust_result);
  };
  known();
 }
}

// The C null-reset postcondition and Rust new/default field postconditions.
// C's null/len!=1 requirements remain obligations of its reset contract.
theorem adler_c_rust_reset(c_result: uint64, rust_a: uint32, rust_b: uint32) {
 requires c_result == 1u64;
 requires rust_a == 1u32;
 requires rust_b == 0u32;
 ensures c_result == (rust_a | (rust_b << 16)) as uint64 by {
  rewrite(c_result, 1u64);
  rewrite(rust_a, 1u32);
  rewrite(rust_b, 0u32);
  normalize();
 }
}
