import click::integer;
import click::rust::slice;

// Original compute bounds for every small-batch length and canonical seeds.
// Length is at most 22207 bytes; both initial fields are below MOD = 65521.
// The stored vector and scalar iterators supply their actual remaining state.
// Verification assembles this contract with checked helpers and arithmetic libraries.

theorem adler_uint64_self_subtract(n: uint64) { ensures n - n == 0u64 by close(); }
theorem adler_equal_byte_read(left: const uint8*, right: const uint8*, index: int32) {
    requires left == right;
    ensures left[index] == right[index] by {
        rewrite(left, right);
        close();
    }
}

theorem adler_stored_sum(value: uint32, left: uint32, right: uint32) {
    requires value == left + right;
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(value) == to_integer(left + right) by {
        rewrite(value, left + right);
        close();
    }
}

theorem adler_equal_stored_words(left: uint32, right: uint32) {
    requires left == right;
    ensures to_integer(left) == to_integer(right) by {
        rewrite(left, right);
        close();
    }
}

theorem adler_recombined_lane_b(total: Integer, seed: Integer, a1: Integer, a2: Integer, a3: Integer, b0: Integer, b1: Integer, b2: Integer, b3: Integer, lane0: Integer, lane1: Integer, lane2: Integer, lane3: Integer) {
    requires total == seed + lane0 + lane1 + lane2 + lane3;
    requires lane0 == b0 * 4;
    requires lane1 == b1 * 4 + (65521 - a1) * 1;
    requires lane2 == b2 * 4 + (65521 - a2) * 2;
    requires lane3 == b3 * 4 + (65521 - a3) * 3;
    ensures total == adler_lane_b(seed, a1, a2, a3, b0, b1, b2, b3) by {
        rewrite(total, seed + lane0 + lane1 + lane2 + lane3);
        rewrite(lane0, b0 * 4);
        rewrite(lane1, b1 * 4 + (65521 - a1) * 1);
        rewrite(lane2, b2 * 4 + (65521 - a2) * 2);
        rewrite(lane3, b3 * 4 + (65521 - a3) * 3);
        unfold(adler_lane_b(seed, a1, a2, a3, b0, b1, b2, b3));
        close() using {};
    }
}

theorem adler_count_nonincreasing(previous: uint64, current: uint64, amount: uint64) {
    requires to_integer(amount) <= to_integer(previous);
    requires current == previous - amount;
    ensures to_integer(current) <= to_integer(previous) by {
        apply(integer::uint64_subtract_to_integer(previous, amount));
        have to_integer(current) == to_integer(previous) - to_integer(amount) by {
            rewrite(current, previous - amount);
            close();
        }
        have 0 <= to_integer(amount) by close();
        have to_integer(previous) - to_integer(amount) <= to_integer(previous) by close() using { 0 <= to_integer(amount); };
        apply(integer::le_substitute(to_integer(previous) - to_integer(amount), to_integer(previous), to_integer(current), to_integer(previous)));
    }
}

theorem adler_signed_count_decrease(previous: uint64, current: uint64, amount: uint64) {
 requires previous <= 22208u64;
 requires amount <= previous;
 requires current <= previous;
 requires current == previous - amount;
 ensures to_integer(current as uint32 as int32) == to_integer(previous as uint32 as int32) - to_integer(amount) by {
  apply(integer::uint64_less_equal_transitive(current, previous, 22208u64));
  apply(adler_count_observation(previous));
  apply(adler_count_observation(current));
  apply(integer::uint64_subtract_to_integer(previous, amount));
  rewrite(to_integer(current as uint32 as int32), to_integer(current));
  rewrite(current, previous - amount);
  rewrite(to_integer(previous as uint32 as int32), to_integer(previous));
  close();
 }
}

theorem adler_integer_zero_times(value: Integer) {
    ensures 0 * value == 0 by {
        have 0 * value == 0 * value + 0 * value by apply(integer::multiply_add(0, 0, value));
        close() using { 0 * value == 0 * value + 0 * value; };
    }
}

theorem adler_initial_lane_b(seed: Integer) {
    ensures adler_lane_b(seed, 0, 0, 0, 0, 0, 0, 0) == seed + 393126 by {
        unfold(adler_lane_b(seed, 0, 0, 0, 0, 0, 0, 0));
        close() using {};
    }
}

theorem adler_same_signed_index(left: int32, right: int32) {
    requires left == right;
    ensures to_integer(left) == to_integer(right) by {
        rewrite(left, right);
        close();
    }
}

theorem adler_tail_index_after_next(total: int32, previous: int32, current: int32) {
    requires 0 <= current;
    requires 1 <= previous;
    requires previous <= total;
    requires total <= 22207;
    requires current == previous - 1;
    ensures (total - current) - 1 == total - previous by {
        rewrite(current, previous - 1);
        close() using { 1 <= previous; previous <= total; total <= 22207; };
    }
}

theorem adler_narrow_residue(value: uint32) {
    requires to_integer(value) < 65521;
    ensures to_integer(value as uint16) == to_integer(value) by {
        apply(integer::lt_step_le(to_integer(value), 65521));
        have to_integer(value) <= 65535 by close() using { to_integer(value) + 1 <= 65521; };
        apply(integer::to_uint16_round_trip(to_integer(value)));
        close();
    }
}
theorem adler_uint16_below_mod(value: uint16) {
    requires to_integer(value) < 65521;
    ensures value < 65521 by {
        have to_integer((65521 as uint16)) == 65521;
        close() using { to_integer(value) < 65521; to_integer((65521 as uint16)) == 65521; };
    }
}
theorem adler_bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22200;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by close() using { 0 <= index; index <= 22200; };
  apply(integer::uint8_pointer_add_associate_int32(base, index, 4));
 }
}
theorem adler_scalar_batch_product_bound(length: uint32, seed: uint32) {
 requires length <= 22204u32;
 requires seed <= 65520u32;
 ensures to_integer(length) * to_integer(seed) <= 1454806080 by {
  have 0 <= to_integer(length);
  have to_integer(length) <= 4294967295;
  have 0 <= to_integer(seed);
  have to_integer(seed) <= 4294967295;
  close() using { 0 <= to_integer(length); to_integer(length) <= 22204; 0 <= to_integer(seed); to_integer(seed) <= 65520; };
 }
}
theorem adler_small_length_cast(length: uint64) {
 requires length <= 22204u64;
 ensures (length as u32) <= 22204u32 and to_integer((length as u32)) == to_integer(length) by {
  have 0u64 <= length by close();
  have 0 <= to_integer(length) by close();
  have to_integer(length) <= 4294967295 by close() using { to_integer(length) <= 22204; };
  have to_integer((length as u32)) == to_integer(length) by {
   close() using { 0 <= to_integer(length); to_integer(length) <= 4294967295; };
  }
  have to_integer((length as u32)) <= to_integer(22204u32) by { rewrite(to_integer((length as u32)), to_integer(length)); close(); }
  close();
 }
}



theorem adler_tail_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22206;
 ensures (base + index) + 1 == base + (index + 1) by {
  have defined(index + 1) by close() using { 0 <= index; index <= 22206; };
  apply(integer::uint8_pointer_add_associate_int32(base, index, 1));
 }
}

// The remainder chunk loop counts whole four-byte chunks (`iter.len()`); the lane
// lemmas count remaining bytes. `adler_chunk_bytes` names that byte count.
function adler_chunk_bytes(count: uint64) -> uint64 { count * 4u64 }

theorem adler_chunk_bytes_value(count: uint64) {
 requires count <= 5551u64;
 ensures to_integer(adler_chunk_bytes(count)) == to_integer(count) * 4 by {
  unfold(adler_chunk_bytes(count));
  close();
 }
}
theorem adler_quarter_exact(p: uint64) {
 requires p % 4u64 == 0u64;
 ensures to_integer(p / 4u64) * 4 == to_integer(p) by {
  apply(integer::uint64_divide_to_integer(p, 4u64));
  apply(integer::uint64_remainder_to_integer(p, 4u64));
  apply(integer::truncation_identity(to_integer(p), 4));
  have to_integer(p % 4u64) == 0;
  close();
 }
}
theorem adler_chunk_bytes_initial(p: uint64) {
 requires p % 4u64 == 0u64;
 requires to_integer(p) <= 22204;
 ensures adler_chunk_bytes(p / 4u64) == p by {
  apply(adler_quarter_exact(p));
  have to_integer(p / 4u64) <= 5551;
  have p / 4u64 <= 5551u64;
  apply(adler_chunk_bytes_value(p / 4u64));
  have to_integer(adler_chunk_bytes(p / 4u64)) == to_integer(p);
  close();
 }
}
theorem adler_chunk_bytes_step(count: uint64) {
 requires 0u64 < count;
 requires count <= 5551u64;
 ensures 4u64 <= adler_chunk_bytes(count) by {
  apply(adler_chunk_bytes_value(count));
  have 4 <= to_integer(adler_chunk_bytes(count));
  close();
 }
 ensures adler_chunk_bytes(count - 1u64) == adler_chunk_bytes(count) - 4u64 by {
  apply(adler_chunk_bytes_value(count));
  have to_integer(count - 1u64) == to_integer(count) - 1;
  have to_integer(count - 1u64) <= to_integer(5551u64);
  apply(adler_chunk_bytes_value(count - 1u64));
  close();
 }
}
theorem adler_chunk_bytes_zero() {
 ensures adler_chunk_bytes(0u64) == 0u64 by { unfold(adler_chunk_bytes(0u64)); close(); }
}
theorem adler_chunk_bytes_position(p: uint64, count: uint64) {
 requires p % 4u64 == 0u64;
 requires to_integer(p) <= 22204;
 requires count <= p / 4u64;
 ensures to_integer((p / 4u64 - count) * 4u64) == to_integer(p - adler_chunk_bytes(count)) by {
  apply(adler_quarter_exact(p));
  have to_integer(p / 4u64) <= 5551;
  have count <= 5551u64;
  apply(adler_chunk_bytes_value(count));
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  have to_integer((p / 4u64 - count) * 4u64) == to_integer(p / 4u64 - count) * 4;
  have to_integer(p - adler_chunk_bytes(count)) == to_integer(p) - to_integer(adler_chunk_bytes(count));
  close();
 }
}
theorem adler_small_outer_quotient(n: uint64) {
 requires to_integer(n) <= 22204;
 ensures n / 22208u64 == 0u64 by {
  have 0 <= to_integer(n);
  have 0 * 22208 <= to_integer(n);
  have to_integer(n) < 1 * 22208;
  apply(integer::positive_divisor_quotient_lower(to_integer(n), 22208, 0));
  apply(integer::positive_divisor_quotient_strict_upper(to_integer(n), 22208, 1));
  apply(integer::uint64_divide_to_integer(n, 22208u64));
  have to_integer(n / 22208u64) == 0;
  close();
 }
}
theorem adler_remainder_chunk_step(p: uint64, count: uint64, passes: Integer) {
 requires p % 4u64 == 0u64;
 requires to_integer(p) <= 22204;
 requires 0u64 < count;
 requires 0 <= passes;
 requires to_integer(count) + passes == to_integer(p / 4u64);
 ensures count <= p / 4u64 by close();
 ensures to_integer(p / 4u64 - count) == passes by {
  have count <= p / 4u64;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  close();
 }
 ensures to_integer(p / 4u64 - count) == passes + to_integer(0u64) by {
  have count <= p / 4u64;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  close();
 }
 ensures p / 4u64 - count < p / 4u64 by {
  have count <= p / 4u64;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  have to_integer(p / 4u64 - count) < to_integer(p / 4u64);
  close();
 }
 ensures to_integer(p / 4u64 - count) < to_integer(p / 4u64) by {
  have count <= p / 4u64;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  close();
 }
 ensures count <= 5551u64 by {
  apply(adler_quarter_exact(p));
  have to_integer(p / 4u64) <= 5551;
  close();
 }
 ensures to_integer((p / 4u64 - count) * 4u64) < to_integer(p) by {
  apply(adler_quarter_exact(p));
  have count <= p / 4u64;
  have to_integer(p / 4u64) <= 5551;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  have to_integer((p / 4u64 - count) * 4u64) == to_integer(p / 4u64 - count) * 4;
  close();
 }
 ensures to_integer((p / 4u64 - count) * 4u64 + 3u64) < to_integer(p) by {
  apply(adler_quarter_exact(p));
  have count <= p / 4u64;
  have to_integer(p / 4u64) <= 5551;
  have to_integer(p / 4u64 - count) == to_integer(p / 4u64) - to_integer(count);
  have to_integer((p / 4u64 - count) * 4u64) == to_integer(p / 4u64 - count) * 4;
  have to_integer((p / 4u64 - count) * 4u64 + 3u64) == to_integer((p / 4u64 - count) * 4u64) + 3;
  close();
 }
}
theorem adler_chunk_bytes_next(count: uint64, next: uint64) {
 requires 0u64 < count;
 requires count <= 5551u64;
 requires to_integer(next) == to_integer(count) - 1;
 ensures to_integer(adler_chunk_bytes(next)) == to_integer(adler_chunk_bytes(count)) - 4 by {
  apply(adler_chunk_bytes_value(count));
  have next <= 5551u64;
  apply(adler_chunk_bytes_value(next));
  close();
 }
}
theorem adler_uint64_pointer_association(base: const uint8*, p: uint64, q: uint64) {
 requires to_integer(p) + to_integer(q) <= 18446744073709551615;
 ensures (base + p) + q == base + (p + q) by {
  apply(integer::uint64_add_to_integer(p, q));
  close() using { to_integer(p + q) == to_integer(p) + to_integer(q); };
 }
}
theorem adler_tail_pointer_position(base: const uint8*, p: uint64, n: uint64, r: uint64) {
 requires to_integer(p) <= to_integer(n);
 requires to_integer(r) <= to_integer(n - p);
 ensures (base + p) + ((n - p) - r) == base + (n - r) by {
  have to_integer(n - p) == to_integer(n) - to_integer(p);
  have to_integer((n - p) - r) == to_integer(n - p) - to_integer(r);
  have to_integer(r) <= to_integer(n);
  have to_integer(n - r) == to_integer(n) - to_integer(r);
  have to_integer(p + ((n - p) - r)) == to_integer(p) + to_integer((n - p) - r);
  have to_integer(p + ((n - p) - r)) == to_integer(n - r);
  have to_integer(p) + to_integer((n - p) - r) <= 18446744073709551615;
  apply(adler_uint64_pointer_association(base, p, (n - p) - r));
  rewrite((base + p) + ((n - p) - r), base + (p + ((n - p) - r)));
  close() using { to_integer(p + ((n - p) - r)) == to_integer(n - r); };
 }
}
theorem adler_tail_read_offset(p: uint64, n: uint64, length: uint64, r: uint64) {
 requires to_integer(p) <= to_integer(n);
 requires to_integer(length) == to_integer(n - p);
 requires 1u64 <= r;
 requires r <= length;
 ensures to_integer(p + (length - r)) < to_integer(n) by {
  have to_integer(n - p) == to_integer(n) - to_integer(p);
  have to_integer(length - r) == to_integer(length) - to_integer(r);
  have to_integer(p) + to_integer(length - r) <= 18446744073709551615;
  apply(integer::uint64_add_to_integer(p, length - r));
  close();
 }
}

impl adler2::Adler32 {
    fn compute(&mut self, bytes: &[u8]) {
     requires bytes.len() <= 22207u64;
     requires bytes.len() < 22208u64;
     requires (self.a as u32) <= 65520u32;
     requires (self.b as u32) <= 65520u32;
     owns self.a;
     owns self.b;
     views *bytes;
     ensures self.a < 65521;
     ensures self.b < 65521;
     ensures to_integer(self.a) == old(adler_spec_a(bytes.as_ptr(), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32)))));
     ensures to_integer(self.b) == old(adler_spec_b(bytes.as_ptr(), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
    } by {
     apply(adler_signed_small_prefix(bytes.len()));
     apply(adler_small_prefix_divisible(bytes.len()));
     apply(adler_native_small_prefix_divisible(bytes.len()));
     apply(adler_small_native_prefix(bytes.len()));
     apply(adler_small_tail_metadata(bytes.len()));
     apply(adler_small_signed_tail(bytes.len()));
     apply(adler_signed_partition_identity(bytes.len()));
     have bytes.len() % 4u64 <= bytes.len() by close();
     have bytes.len() - bytes.len() % 4u64 <= bytes.len();
     apply(adler_small_outer_remainder(bytes.len() - bytes.len() % 4u64));
     have bytes.len() <= 2147483647u64 by { apply(integer::uint64_less_equal_transitive(bytes.len(), 22207u64, 2147483647u64)); }
     have 0 <= old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) by close() using { 0 <= (((bytes.len() - bytes.len() % 4u64) as u32) as i32); };
     have old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22204 by close() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) <= 22204; };
     have old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) % 4 == 0 by close() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) % 4 == 0; };
     have bytes.len() % 4u64 <= bytes.len() by close();
     have bytes.len() - bytes.len() % 4u64 <= bytes.len();
     have bytes.len() - bytes.len() % 4u64 <= 2147483647u64 by close() using { bytes.len() - bytes.len() % 4u64 <= bytes.len(); bytes.len() <= 2147483647u64; };
     have to_integer((bytes.len())) <= to_integer(22207u64);
     have bytes.len() < 22208u64 by close();
     have exists (n: uint64) { n == bytes.len() } by { witness(bytes.len()); close(); }
     let backing_length = obtain(exists (n: uint64) { n == bytes.len() });
     have backing_length <= 22207u64 by {
      rewrite(backing_length, bytes.len());
      close();
     }
     apply(adler_unsigned_small_partition(backing_length));
     apply(adler_native_small_prefix_divisible(backing_length));
     mark input_bytes;
     have forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies at(input_bytes, bytes[k]) == old(bytes[k]) } by {
      intro() { intro() { close(); } }
     }
     step_until(assignment(b, 0).entry); step();
     have a == old((self.a as u32));
     have a <= 65520u32 by { rewrite(a, old((self.a as u32))); close(); }
     have b == old((self.b as u32));
     have b <= 65520u32 by { rewrite(b, old((self.b as u32))); close(); }
     step_until(loop(0).entry);
     have separate(memory((a_vec as (uint8 *))[0..16]), memory(bytes[0u64..bytes.len()])) by close();
     have separate(memory((b_vec as (uint8 *))[0..16]), memory(bytes[0u64..bytes.len()])) by close();
     have loop(0).iter.chunk_size == 22208u64 by close();
     have backing_length == old(bytes.len()) by close();
     have bytes.len() == backing_length - backing_length % 4u64 by {
      rewrite(backing_length, old(bytes.len()));
      close();
     }
     have bytes.len() % 4u64 == 0u64 by {
      rewrite(bytes.len(), backing_length - backing_length % 4u64);
      close() using { (backing_length - backing_length % 4u64) % 4u64 == 0u64; };
     }
     have backing_length % 4u64 <= backing_length by close();
     apply(integer::uint64_subtract_to_integer(backing_length, backing_length % 4u64));
     have to_integer(backing_length) - to_integer(backing_length % 4u64) <= 22204 by {
      apply(integer::le_substitute(to_integer(backing_length - backing_length % 4u64), 22204, to_integer(backing_length) - to_integer(backing_length % 4u64), 22204));
     }
     have to_integer(bytes.len()) <= 22204 by {
      rewrite(bytes.len(), backing_length - backing_length % 4u64);
      close() using { to_integer(backing_length) - to_integer(backing_length % 4u64) <= 22204; };
     }
     apply(adler_small_outer_quotient(bytes.len()));
     have (bytes.len() - bytes.len() % 4u64) / 22208u64 == 0u64 by {
      rewrite(bytes.len() % 4u64, 0u64);
      close() using { bytes.len() / 22208u64 == 0u64; };
     }
     have loop(0).iter.len() == 0u64 by close();
     have remainder_chunk.len() == (bytes.len() - bytes.len() % 4u64) % 22208u64 by close();
     have remainder_chunk.as_ptr() == bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64) by close();
     have ((remainder_chunk.len() as u32) as i32) == old((((bytes.len() - bytes.len() % 4u64) as u32) as i32));
     have to_integer(remainder_chunk.len()) == to_integer(bytes.len() - bytes.len() % 4u64) by { rewrite(remainder_chunk.len(), (bytes.len() - bytes.len() % 4u64) % 22208u64); close(); }
     have to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64);
     have remainder_chunk.len() == bytes.len() - bytes.len() % 4u64;
     have to_integer((bytes.len())) <= to_integer(2147483647u64);

     have to_integer((bytes.len() - bytes.len() % 4u64)) <= to_integer(2147483647u64);
     have to_integer(remainder_chunk.len()) <= to_integer(2147483647u64) by { rewrite(to_integer(remainder_chunk.len()), to_integer(bytes.len() - bytes.len() % 4u64)); close(); }
     have remainder_chunk.len() <= 2147483647u64;
     have remainder_chunk.as_ptr() == bytes.as_ptr() by { rewrite(remainder_chunk.as_ptr(), bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - (bytes.len() - bytes.len() % 4u64) % 22208u64)); rewrite((bytes.len() - bytes.len() % 4u64) % 22208u64, bytes.len() - bytes.len() % 4u64); apply(adler_uint64_self_subtract(bytes.len() - bytes.len() % 4u64)); close(); }
     step_until(loop(2).entry);
     have bytes.as_ptr() == old(bytes.as_ptr()) by close();
     have to_integer(bytes.len()) + to_integer(remainder.len()) <= 18446744073709551615 by close();
     apply(integer::uint64_add_to_integer(bytes.len(), remainder.len()));
     have backing_length == old(bytes.len()) by close();
     have old(bytes.len()) <= 22207u64 by close();
     apply(adler_small_tail_metadata(old(bytes.len())));
     have to_integer(remainder.len()) == to_integer(old(bytes.len()) % 4u64) by close();
     have old(bytes.len()) % 4u64 <= old(bytes.len()) by close();
     apply(integer::uint64_subtract_to_integer(old(bytes.len()), old(bytes.len()) % 4u64));
     have to_integer(bytes.len()) == to_integer(old(bytes.len())) - to_integer(old(bytes.len()) % 4u64) by close();
     have to_integer(backing_length) == to_integer(old(bytes.len())) by close();
     have to_integer(bytes.len()) + to_integer(remainder.len()) == to_integer(backing_length) by close() using {
      to_integer(remainder.len()) == to_integer(old(bytes.len()) % 4u64);
      to_integer(bytes.len()) == to_integer(old(bytes.len())) - to_integer(old(bytes.len()) % 4u64);
      to_integer(backing_length) == to_integer(old(bytes.len()));
     };
     have bytes.len() + remainder.len() == backing_length by close();
     have to_integer(bytes.len()) <= to_integer(backing_length) by {
      have 0 <= to_integer(remainder.len());
      apply(integer::add_le(to_integer(bytes.len()), to_integer(bytes.len()), 0, to_integer(remainder.len())));
      rewrite(to_integer(backing_length), to_integer(bytes.len()) + to_integer(remainder.len()));
      close();
     }
     apply(integer::uint64_to_integer_less_equal_implies_less_equal(bytes.len(), backing_length));
     have backing_length <= 22207u64 by {
      rewrite(backing_length, old(bytes.len()));
      close();
     }
     apply(integer::uint64_less_equal_transitive(bytes.len(), backing_length, 22207u64));
     have forall (k: int32) { 0 <= k and k < ((backing_length as u32) as i32) implies bytes[k] == old(bytes[k]) } by {
      intro() {
       intro() {
        have 0 <= k by close();
        have k < old(((bytes.len() as u32) as i32)) by close();
        have bytes.as_ptr() + k == old(bytes.as_ptr()) + k by { rewrite(bytes.as_ptr(), old(bytes.as_ptr())); close(); }
        have at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) == old(bytes[k]) by close();
        have at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(2).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(2)); }
        have at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
         at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(3).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(3)); }
        have at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(6).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(6)); }
        have at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(7).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(7).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(7).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(7).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(7)); }
        have at(region(7).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(7).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(7).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(7).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(9).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(7).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(9).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(9).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(9).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(9)); }
        have at(region(9).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(9).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(9).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(9).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(7).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(7).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(10).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(9).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(10).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(10).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(10).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(10)); }
        have at(region(10).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(10).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(10).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(10).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(9).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(9).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(11).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(10).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(11).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(11).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(11).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(11)); }
        have at(region(11).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(11).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(11).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(11).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(10).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(10).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(12).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(11).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(12).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(12).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(12).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(12)); }
        have at(region(12).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(12).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(12).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(12).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(11).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(11).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(13).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(12).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(13).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(13).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(13).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(13)); }
        have at(region(13).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(13).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(13).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(13).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(12).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(12).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(14).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(13).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(14).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(14).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(14).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(14)); }
        have at(region(14).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(14).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(14).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(14).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(13).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(13).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(15).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(14).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(15).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(15).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(15).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(15)); }
        have at(region(15).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(15).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(15).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(15).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(14).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(14).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(17).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(15).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(17).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(17).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(17).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(17)); }
        have at(region(17).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(17).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(17).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(17).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(15).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(15).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(18).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(17).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(18).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(18).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(18).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(18)); }
        have at(region(18).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(18).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(18).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(18).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(17).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(17).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(19).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(18).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(19).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(19).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(19).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(19)); }
        have at(region(19).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(19).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(19).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(19).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(18).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(18).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(20).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(19).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(20).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(20).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(20).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(20)); }
        have at(region(20).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(20).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(20).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(20).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(19).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(19).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(21).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(20).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(21).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(21).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(21).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(21)); }
        have at(region(21).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(21).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(21).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(21).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(20).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(20).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(22).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(21).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(22).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(22).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(22).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(22)); }
        have at(region(22).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(22).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(22).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(22).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(21).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(21).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(22).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(23).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(23)); }
        have at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(22).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(22).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(25).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(25).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(25).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(25).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(25)); }
        have at(region(25).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(25).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(25).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(25).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(25).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(26).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(26)); }
        have at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(25).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(25).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(27).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(27).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(27).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(27).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(27)); }
        have at(region(27).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(27).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(27).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(27).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(28).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(27).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(28).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(28).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(28).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(28)); }
        have at(region(28).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(28).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(28).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(28).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(27).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(27).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(29).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(28).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(29).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(29).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(29).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(29)); }
        have at(region(29).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(29).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(29).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(29).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(28).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(28).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(32).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(29).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(32).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(32).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(32).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(32)); }
        have at(region(32).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(32).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(32).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(32).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(29).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(29).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(33).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(32).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(33).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(33).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(33).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(33)); }
        have at(region(33).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(33).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(33).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(33).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(32).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(32).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(34).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(33).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(34).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(34).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(34).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(34)); }
        have at(region(34).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(34).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(34).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(34).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(33).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(33).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(35).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(34).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(35).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(35).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(35).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(35)); }
        have at(region(35).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(35).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(35).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(35).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(34).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(34).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(36).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(35).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(36).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(36).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(36).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(36)); }
        have at(region(36).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(36).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(36).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(36).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(35).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(35).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(38).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(36).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(38).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(38).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(38).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(38)); }
        have at(region(38).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(38).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(38).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(38).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(36).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(36).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(39).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(38).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(39).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(39).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(39).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(39)); }
        have at(region(39).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(39).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(39).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(39).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(38).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(38).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(40).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(39).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(40).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(40).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(40).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(40)); }
        have at(region(40).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(40).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(40).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(40).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(39).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(39).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(41).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(40).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(41).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(41).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(41).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(41)); }
        have at(region(41).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(41).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(41).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(41).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(40).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(40).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(42).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(41).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(42).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(42).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(42).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(42)); }
        have at(region(42).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(42).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(42).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(42).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(41).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(41).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(43).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(42).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(43).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(43).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(43).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(43)); }
        have at(region(43).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(43).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(43).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(43).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(42).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(42).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(44).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(43).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(44).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(44).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(44).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(44)); }
        have at(region(44).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(44).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(44).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(44).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(43).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(43).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(45).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(44).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(45).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(45).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(45).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(45)); }
        have at(region(45).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(45).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(45).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(45).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(44).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(44).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(46).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(45).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(46).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(46).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(46).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(46)); }
        have at(region(46).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(46).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(46).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(46).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(45).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(45).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(60).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(46).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(60).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(60).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(60).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(60)); }
        have at(region(60).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(60).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(60).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(60).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(46).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(46).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(65).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(60).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(65).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(65).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(65).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(65)); }
        have at(region(65).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(65).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(65).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(65).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(60).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(60).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(86).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(65).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(86).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(86).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(86).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(86)); }
        have at(region(86).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(86).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(86).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(86).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(65).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(65).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(87).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(86).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(87).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(87).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(87).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(87)); }
        have at(region(87).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(87).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(87).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(87).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(86).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(86).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        rewrite(bytes.as_ptr() + k, old(bytes.as_ptr()) + k);
        have load<uint8>(old(bytes.as_ptr()) + k) == at(region(87).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        close() using {
         load<uint8>(old(bytes.as_ptr()) + k) == at(region(87).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(87).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
         at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) == old(bytes[k]);
        };
       }
      }
     }
     have loop(2).iter.chunk_size == 4u64 by close();
     have remainder_chunk.len() % 4u64 == 0u64 by {
      rewrite(remainder_chunk.len(), bytes.len() - bytes.len() % 4u64);
      close();
     }
     have loop(2).iter.v.len() == remainder_chunk.len() - remainder_chunk.len() % 4u64 by close();
     have loop(2).iter.v.len() == bytes.len() - bytes.len() % 4u64 by {
      rewrite(loop(2).iter.v.len(), remainder_chunk.len() - remainder_chunk.len() % 4u64);
      rewrite(remainder_chunk.len() % 4u64, 0u64);
      rewrite(remainder_chunk.len(), bytes.len() - bytes.len() % 4u64);
      close();
     }
     have loop(2).iter.len() == loop(2).iter.v.len() / 4u64 by close();
     have loop(2).iter.len() == (bytes.len() - bytes.len() % 4u64) / 4u64 by {
      rewrite(loop(2).iter.len(), loop(2).iter.v.len() / 4u64);
      rewrite(loop(2).iter.v.len(), bytes.len() - bytes.len() % 4u64);
      close();
     }
     have loop(2).iter.v == remainder_chunk by close();
     have adler_chunk_bytes(loop(2).iter.len()) == bytes.len() - bytes.len() % 4u64 by {
      apply(adler_chunk_bytes_initial(bytes.len() - bytes.len() % 4u64));
      rewrite(loop(2).iter.len(), (bytes.len() - bytes.len() % 4u64) / 4u64);
      close();
     }
     have ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by { rewrite(adler_chunk_bytes(loop(2).iter.len()), bytes.len() - bytes.len() % 4u64); close(); }
     have bytes.as_ptr() == old(bytes.as_ptr());
     apply(adler_lane_initial_ceiling());
     apply(adler_lane_iterator_initial(old((((bytes.len() - bytes.len() % 4u64) as u32) as i32))));
     have adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)) == 0 by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32))); close(); }
     have to_integer(a_vec.0[0]) == 0;
     have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); rewrite(to_integer(a_vec.0[0]), 0); close() using {}; }
     have to_integer(b_vec.0[0]) == 0;
     have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); rewrite(to_integer(b_vec.0[0]), 0); close() using {}; }
     have to_integer(a_vec.0[1]) == 0;
     have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); rewrite(to_integer(a_vec.0[1]), 0); close() using {}; }
     have to_integer(b_vec.0[1]) == 0;
     have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); rewrite(to_integer(b_vec.0[1]), 0); close() using {}; }
     have to_integer(a_vec.0[2]) == 0;
     have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); rewrite(to_integer(a_vec.0[2]), 0); close() using {}; }
     have to_integer(b_vec.0[2]) == 0;
     have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); rewrite(to_integer(b_vec.0[2]), 0); close() using {}; }
     have to_integer(a_vec.0[3]) == 0;
     have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_a_ceiling(0), 65520); rewrite(to_integer(a_vec.0[3]), 0); close() using {}; }
     have to_integer(b_vec.0[3]) == 0;
     have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by { rewrite(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_b_ceiling(0), 65520); rewrite(to_integer(b_vec.0[3]), 0); close() using {}; }
     have 0 <= ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32))); close(); }
     have ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32))); close() using {}; }
     have 0 <= ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) and ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by close();
     have ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) % 4 == 0 by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32))); close(); }
     have adler_chunk_bytes(loop(2).iter.len()) <= bytes.len() - bytes.len() % 4u64 by { rewrite(adler_chunk_bytes(loop(2).iter.len()), bytes.len() - bytes.len() % 4u64); close(); }
     have adler_chunk_bytes(loop(2).iter.len()) % 4u64 == 0u64 by { rewrite(adler_chunk_bytes(loop(2).iter.len()), bytes.len() - bytes.len() % 4u64); close(); }
     have (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(loop(2).iter.len()) == 0u64 by close() using { adler_chunk_bytes(loop(2).iter.len()) == bytes.len() - bytes.len() % 4u64; };
     have bytes.len() < 22208u64 by close();
     have bytes.len() == old(bytes.len() - bytes.len() % 4u64) by close();
     have 0 <= to_integer(a);
     have to_integer(a) <= 4294967295;
     have to_integer(a) <= to_integer(65520u32);
     apply(adler_spec_empty(bytes.as_ptr(), to_integer(a), 0));
     have ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)) == 0 by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), (((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); close(); }
     have adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) == to_integer(a) by { unfold(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); close(); }
     have to_integer(a) == 0 * 65521 + to_integer(a) by close() using {};
     apply(adler_residue_unique(to_integer(a), 0, to_integer(a)));
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes.as_ptr(), ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), to_integer(a)) by { rewrite(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); rewrite(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), to_integer(a)); apply(integer::equal_substitute(to_integer(a), to_integer(a), truncating_remainder(to_integer(a), 65521), adler_spec_a(bytes.as_ptr(), 0, to_integer(a)))); }
     have 0 <= to_integer(b);
     have to_integer(b) <= 4294967295;
     have to_integer(b) <= to_integer(65520u32);
     apply(adler_spec_empty(bytes.as_ptr(), to_integer(a), to_integer(b)));
     have to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) == 0 by close() using { ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)) == 0; };
     have adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) == to_integer(b) + 393126 by { rewrite(to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))), 0);
      apply(adler_integer_zero_times(to_integer(a)));
      rewrite(0 * to_integer(a), 0);
      have to_integer(b) + 0 == to_integer(b) by close();
      rewrite(to_integer(b) + 0, to_integer(b));
      rewrite(to_integer(a_vec.0[1]), 0);
      rewrite(to_integer(a_vec.0[2]), 0);
      rewrite(to_integer(a_vec.0[3]), 0);
      rewrite(to_integer(b_vec.0[0]), 0);
      rewrite(to_integer(b_vec.0[1]), 0);
      rewrite(to_integer(b_vec.0[2]), 0);
      rewrite(to_integer(b_vec.0[3]), 0);
      apply(adler_initial_lane_b(to_integer(b)));
     }
     have 0 <= to_integer(b) + 393126 by close() using { 0 <= to_integer(b); };
     have 0 <= adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), to_integer(b) + 393126); close(); }
     have to_integer(b) + 393126 == 6 * 65521 + to_integer(b) by close() using {};
     apply(adler_residue_unique(to_integer(b) + 393126, 6, to_integer(b)));
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes.as_ptr(), ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), to_integer(a), to_integer(b)) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), to_integer(b) + 393126); rewrite(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), 0); apply(integer::equal_substitute(to_integer(b), to_integer(b), truncating_remainder(to_integer(b) + 393126, 65521), adler_spec_b(bytes.as_ptr(), 0, to_integer(a), to_integer(b)))); }
     have defined(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - (((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)));
     have separate(memory((a_vec as (uint8 *))[0..16]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     have separate(memory((b_vec as (uint8 *))[0..16]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     loop {
      decreases iter.len();
      owns a_vec.0[0..4];
      owns b_vec.0[0..4];
      views *bytes;
      invariant bytes.len() <= 22207u64;
      invariant bytes.len() < 22208u64;
      invariant bytes.len() - bytes.len() % 4u64 <= 22204u64;
      invariant bytes.as_ptr() == old(bytes.as_ptr());
      invariant forall (k: int32) { 0 <= k and k < ((backing_length as u32) as i32) implies bytes[k] == old(bytes[k]) };
      invariant bytes.len() == old(bytes.len() - bytes.len() % 4u64);
      invariant bytes.len() % 4u64 == 0u64;
      invariant bytes.len() + remainder.len() == backing_length;
      invariant a <= 65520u32;
      invariant b <= 65520u32;
      invariant 0 <= old((((bytes.len() - bytes.len() % 4u64) as u32) as i32));
      invariant old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22204;
      invariant old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) % 4 == 0;
      invariant 0 <= ((adler_chunk_bytes(iter.len()) as uint32) as int32) and ((adler_chunk_bytes(iter.len()) as uint32) as int32) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32));
      invariant truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes.as_ptr(), ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), to_integer(a));
      invariant 0 <= adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3]));
      invariant truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes.as_ptr(), ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), to_integer(a), to_integer(b));
      invariant iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()));
      invariant iter.chunk_size == 4u64;
      invariant ((adler_chunk_bytes(iter.len()) as uint32) as int32) % 4 == 0;
      invariant adler_chunk_bytes(iter.len()) <= bytes.len() - bytes.len() % 4u64;
      invariant adler_chunk_bytes(iter.len()) % 4u64 == 0u64;
      invariant to_integer(iter.len()) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 4u64);
      invariant to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      invariant to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
      maintain by {
       step(); step(); step(); step();
       have 4u64 <= loop(2).iter.v.len() by close();
       have 4 <= to_integer(loop(2).iter.v.len()) by close();
       apply(integer::positive_divisor_quotient_lower(to_integer(loop(2).iter.v.len()), 4, 1));
       apply(integer::uint64_divide_to_integer(loop(2).iter.v.len(), 4u64));
       have 1 <= to_integer(iter.len()) by close();
       have 0u64 < iter.len() by close() using { 1 <= to_integer(iter.len()); };
       have 0 <= iterations;
       apply(adler_remainder_chunk_step(bytes.len() - bytes.len() % 4u64, iter.len(), iterations));
       have iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len())) by close();
       have iter.chunk_size == 4u64 by close();
       apply(adler_chunk_bytes_step(iter.len()));
       apply(adler_chunk_bytes_position(bytes.len() - bytes.len() % 4u64, iter.len()));
       have to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(bytes.len());
       have to_integer(((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len()) * 4u64) < to_integer(bytes.len()) by close() using { to_integer(((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len()) * 4u64) < to_integer(bytes.len() - bytes.len() % 4u64); to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(bytes.len()); };
       have to_integer(((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len()) * 4u64 + 3u64) < to_integer(bytes.len()) by close() using { to_integer(((bytes.len() - bytes.len() % 4u64) / 4u64 - iter.len()) * 4u64 + 3u64) < to_integer(bytes.len() - bytes.len() % 4u64); to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(bytes.len()); };
       have 4u64 <= adler_chunk_bytes(iter.len());
       have adler_chunk_bytes(iter.len()) <= 22208u64 by close() using { adler_chunk_bytes(iter.len()) <= bytes.len() - bytes.len() % 4u64; bytes.len() - bytes.len() % 4u64 <= 22204u64; };
       apply(adler_count_lane_step(adler_chunk_bytes(iter.len())));
       have exists (n: int32) { n == ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) } by { witness(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))); close(); }
       let prefix_model_count = obtain(exists (n: int32) { n == ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) });
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes.as_ptr(), prefix_model_count, to_integer(a)) by { rewrite(prefix_model_count, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))); close(); }
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(prefix_model_count) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes.as_ptr(), prefix_model_count, to_integer(a), to_integer(b)) by { rewrite(prefix_model_count, ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))); close(); }
       mark lane_head;
       have at(lane_head, truncating_remainder(adler_lane_b(to_integer(b) + to_integer(prefix_model_count) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes.as_ptr(), prefix_model_count, to_integer(a), to_integer(b))) by close();
       have at(lane_head, truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes.as_ptr(), prefix_model_count, to_integer(a))) by close();
       have at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) % 4 == 0;
       have at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32));
       have 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32));
       have 0 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32));
       have old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22208 by { apply(integer::int32_less_equal_transitive(old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)), 22204, 22208)); }
       have 4u64 <= at(lane_head, adler_chunk_bytes(iter.len()));
       have at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() - bytes.len() % 4u64;
       have bytes.len() - bytes.len() % 4u64 <= bytes.len();
       have (bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() by close() using { at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() - bytes.len() % 4u64; bytes.len() - bytes.len() % 4u64 <= bytes.len(); };
       have 4u64 <= bytes.len() - ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) by close() using { 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() - bytes.len() % 4u64; bytes.len() - bytes.len() % 4u64 <= bytes.len(); };
       have 0 <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close() using { 0 <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; 0 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have (old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))) + 4 <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by close() using { 0 <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       step_until(loop(2).statement(0).entry);
       have byte_vec.len() == 4u64;
       have byte_vec.as_ptr() == bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())));
       have loop(2).iter.v == byte_vec + 4u64 by close();
       have 4u64 <= at(lane_head, iter.v.len()) by close();
       have iter.v.len() == at(lane_head, iter.v.len()) - 4u64 by close();
       apply(integer::uint64_subtract_to_integer(at(lane_head, iter.v.len()), 4u64));
       have to_integer(iter.v.len()) + 4 * 1 == to_integer(at(lane_head, iter.v.len())) by {
        rewrite(iter.v.len(), at(lane_head, iter.v.len()) - 4u64);
        rewrite(to_integer(at(lane_head, iter.v.len()) - 4u64), to_integer(at(lane_head, iter.v.len())) - 4);
        close();
       }
       apply(integer::nonnegative_quotient_shift(to_integer(iter.v.len()), 4, 1));
       apply(integer::uint64_divide_to_integer(iter.v.len(), 4u64));
       apply(integer::uint64_divide_to_integer(at(lane_head, iter.v.len()), 4u64));
       have to_integer(at(lane_head, iter.len())) == to_integer(iter.len()) + 1 by {
        rewrite(to_integer(at(lane_head, iter.v.len()) / 4u64), truncating_quotient(to_integer(at(lane_head, iter.v.len())), 4));
        rewrite(to_integer(iter.v.len() / 4u64), truncating_quotient(to_integer(iter.v.len()), 4));
        rewrite(to_integer(at(lane_head, iter.v.len())), to_integer(iter.v.len()) + 4 * 1);
        close();
       }
       have 1u64 <= at(lane_head, iter.len()) by close();
       apply(integer::uint64_subtract_to_integer(at(lane_head, iter.len()), 1u64));
       have iter.len() == at(lane_head, iter.len()) - 1u64 by close() using {
        to_integer(at(lane_head, iter.len())) == to_integer(iter.len()) + 1;
        to_integer(at(lane_head, iter.len()) - 1u64) == to_integer(at(lane_head, iter.len())) - 1;
       };
       have 0u64 < at(lane_head, iter.len());
       have at(lane_head, iter.len()) <= 5551u64;
       have to_integer(iter.len()) == to_integer(at(lane_head, iter.len())) - 1;
       apply(adler_chunk_bytes_next(at(lane_head, iter.len()), iter.len()));
       have adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64;
       have at(lane_head, adler_chunk_bytes(iter.len())) <= 22208u64;
       have at(lane_head, adler_chunk_bytes(iter.len())) <= 2147483647u64 by { apply(integer::uint64_less_equal_transitive(at(lane_head, adler_chunk_bytes(iter.len())), 22208u64, 2147483647u64)); }
       have adler_chunk_bytes(iter.len()) <= 2147483647u64 by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; at(lane_head, adler_chunk_bytes(iter.len())) <= 22208u64; };
       apply(adler_index_observation(at(lane_head, adler_chunk_bytes(iter.len()))));
       apply(adler_index_observation(adler_chunk_bytes(iter.len())));
       apply(adler_count_nonincreasing(at(lane_head, adler_chunk_bytes(iter.len())), adler_chunk_bytes(iter.len()), 4u64));
       apply(integer::uint64_to_integer_less_equal_implies_less_equal(adler_chunk_bytes(iter.len()), at(lane_head, adler_chunk_bytes(iter.len()))));
       apply(adler_signed_count_decrease(at(lane_head, adler_chunk_bytes(iter.len())), adler_chunk_bytes(iter.len()), 4u64));
       have defined(at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) by close();
       apply(integer::int32_subtract_to_integer(at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), 4));
       have ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4 by close() using {
        to_integer(((adler_chunk_bytes(iter.len()) as uint32) as int32)) == to_integer(at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))) - 4;
        to_integer(at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) == to_integer(at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))) - 4;
       };
       apply(adler_signed_small_prefix(bytes.len()));
       apply(adler_small_signed_tail(bytes.len()));
       apply(adler_signed_partition_identity(bytes.len()));
       have (((bytes.len() - bytes.len() % 4u64) as u32) as i32) == old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) by {
        rewrite(bytes.len() % 4u64, 0u64);
        have bytes.len() - 0u64 == bytes.len() by close();
        rewrite(bytes.len() - 0u64, bytes.len());
        rewrite(bytes.len(), old(bytes.len() - bytes.len() % 4u64));
        close();
       }
       apply(adler_small_prefix_within_full(bytes.len()));
       have 0 <= ((bytes.len() as u32) as i32) by close();
       have ((bytes.len() as u32) as i32) <= 22207 by close();
       have old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= ((bytes.len() as u32) as i32) by close() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) == old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)); (((bytes.len() - bytes.len() % 4u64) as u32) as i32) <= ((bytes.len() as u32) as i32); };
       have adler_chunk_bytes(iter.len()) <= (bytes.len() - bytes.len() % 4u64) by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= (bytes.len() - bytes.len() % 4u64); };
       have 4u64 <= (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= (bytes.len() - bytes.len() % 4u64); };
       have (bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())) == (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64 by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); at(lane_head, adler_chunk_bytes(iter.len())) <= (bytes.len() - bytes.len() % 4u64); };
       have byte_vec.as_ptr() == bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64) by { rewrite(byte_vec.as_ptr(), bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())))); rewrite((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())), (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64); close(); }
       have 0 <= ((adler_chunk_bytes(iter.len()) as uint32) as int32) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; };
       have ((adler_chunk_bytes(iter.len()) as uint32) as int32) <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have 4 <= (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have (((bytes.len() - bytes.len() % 4u64) as u32) as i32) <= 22204 by close() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) == old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)); old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22204; };
       step_until(statement(10).statement(0).call(0).entry);
       let { result: loaded_lanes } = step();
       mark from_call;
       have load<uint32>(loaded_lanes) == (byte_vec[0] as u32) by close();
       have load<uint32>(byte_offset(loaded_lanes, 4)) == (byte_vec[1] as u32) by close();
       have load<uint32>(byte_offset(loaded_lanes, 8)) == (byte_vec[2] as u32) by close();
       have load<uint32>(byte_offset(loaded_lanes, 12)) == (byte_vec[3] as u32) by close();
       have byte_vec[0] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] by {
        apply(adler_equal_byte_read(byte_vec, bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64), 0));
       }
       have byte_vec[1] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] by {
        apply(adler_equal_byte_read(byte_vec, bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64), 1));
       }
       have byte_vec[2] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] by {
        apply(adler_equal_byte_read(byte_vec, bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64), 2));
       }
       have byte_vec[3] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] by {
        apply(adler_equal_byte_read(byte_vec, bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64), 3));
       }
       step_until(loop(2).statement(1).entry);
       mark vector_a;
       have at(vector_a, b_vec.0[0]) == at(lane_head, b_vec.0[0]) by close();
       have at(vector_a, b_vec.0[1]) == at(lane_head, b_vec.0[1]) by close();
       have at(vector_a, b_vec.0[2]) == at(lane_head, b_vec.0[2]) by close();
       have at(vector_a, b_vec.0[3]) == at(lane_head, b_vec.0[3]) by close();
       have at(vector_a, a_vec.0[0]) == at(lane_head, a_vec.0[0]) by close();
       have at(vector_a, a_vec.0[1]) == at(lane_head, a_vec.0[1]) by close();
       have at(vector_a, a_vec.0[2]) == at(lane_head, a_vec.0[2]) by close();
       have at(vector_a, a_vec.0[3]) == at(lane_head, a_vec.0[3]) by close();
       have val.0[0] == at(from_call, (byte_vec[0] as u32)) by close();
       have val.0[1] == at(from_call, (byte_vec[1] as u32)) by close();
       have val.0[2] == at(from_call, (byte_vec[2] as u32)) by close();
       have val.0[3] == at(from_call, (byte_vec[3] as u32)) by close();
       have byte_vec[0] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] by {
        apply(adler_equal_byte_read(byte_vec, bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64), 0));
       }
       have byte_vec[1] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] by {
        apply(adler_equal_byte_read(byte_vec, bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64), 1));
       }
       have byte_vec[2] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] by {
        apply(adler_equal_byte_read(byte_vec, bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64), 2));
       }
       have byte_vec[3] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] by {
        apply(adler_equal_byte_read(byte_vec, bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64), 3));
       }
       have at(vector_a, val.0[0]) == at(vector_a, (byte_vec[0] as u32)) by close() using { val.0[0] == at(from_call, (byte_vec[0] as u32)); at(from_call, byte_vec[0]) == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0]; byte_vec[0] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0]; };
       apply(adler_helper_byte_observation(at(vector_a, byte_vec[0])));
       have to_integer(at(vector_a, val.0[0])) == at(vector_a, to_integer((byte_vec[0] as i32))) by {
        rewrite(at(vector_a, val.0[0]), at(vector_a, (byte_vec[0] as u32)));
        close() using { at(vector_a, to_integer((byte_vec[0] as u32))) == at(vector_a, to_integer((byte_vec[0] as i32))); };
       }
       have at(vector_a, val.0[1]) == at(vector_a, (byte_vec[1] as u32)) by close() using { val.0[1] == at(from_call, (byte_vec[1] as u32)); at(from_call, byte_vec[1]) == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1]; byte_vec[1] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1]; };
       apply(adler_helper_byte_observation(at(vector_a, byte_vec[1])));
       have to_integer(at(vector_a, val.0[1])) == at(vector_a, to_integer((byte_vec[1] as i32))) by {
        rewrite(at(vector_a, val.0[1]), at(vector_a, (byte_vec[1] as u32)));
        close() using { at(vector_a, to_integer((byte_vec[1] as u32))) == at(vector_a, to_integer((byte_vec[1] as i32))); };
       }
       have at(vector_a, val.0[2]) == at(vector_a, (byte_vec[2] as u32)) by close() using { val.0[2] == at(from_call, (byte_vec[2] as u32)); at(from_call, byte_vec[2]) == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2]; byte_vec[2] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2]; };
       apply(adler_helper_byte_observation(at(vector_a, byte_vec[2])));
       have to_integer(at(vector_a, val.0[2])) == at(vector_a, to_integer((byte_vec[2] as i32))) by {
        rewrite(at(vector_a, val.0[2]), at(vector_a, (byte_vec[2] as u32)));
        close() using { at(vector_a, to_integer((byte_vec[2] as u32))) == at(vector_a, to_integer((byte_vec[2] as i32))); };
       }
       have at(vector_a, val.0[3]) == at(vector_a, (byte_vec[3] as u32)) by close() using { val.0[3] == at(from_call, (byte_vec[3] as u32)); at(from_call, byte_vec[3]) == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3]; byte_vec[3] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3]; };
       apply(adler_helper_byte_observation(at(vector_a, byte_vec[3])));
       have to_integer(at(vector_a, val.0[3])) == at(vector_a, to_integer((byte_vec[3] as i32))) by {
        rewrite(at(vector_a, val.0[3]), at(vector_a, (byte_vec[3] as u32)));
        close() using { at(vector_a, to_integer((byte_vec[3] as u32))) == at(vector_a, to_integer((byte_vec[3] as i32))); };
       }
       have to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64);
       have to_integer(adler_chunk_bytes(iter.len())) <= to_integer(bytes.len() - bytes.len() % 4u64) by close() using { adler_chunk_bytes(iter.len()) <= (bytes.len() - bytes.len() % 4u64); to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64); };
       apply(integer::uint64_subtract_to_integer(bytes.len() - bytes.len() % 4u64, adler_chunk_bytes(iter.len())));
       have to_integer(4u64) <= to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len())) by close() using { 4u64 <= (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()); to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64); to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len())) == to_integer(bytes.len() - bytes.len() % 4u64) - to_integer(adler_chunk_bytes(iter.len())); };
       have to_integer(bytes.len() - bytes.len() % 4u64) <= to_integer(22204u64) by close() using { bytes.len() - bytes.len() % 4u64 <= 22204u64; to_integer(bytes.len() - bytes.len() % 4u64) == to_integer(bytes.len()) - to_integer(bytes.len() % 4u64); };
       apply(adler_count_previous_chunk_byte_observation(bytes.as_ptr(), (bytes.len() - bytes.len() % 4u64), adler_chunk_bytes(iter.len()), 0));
       have at(vector_a, byte_vec[0]) == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] by close() using { byte_vec[0] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0]; };
       have at(vector_a, to_integer((byte_vec[0] as int32))) == to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] as int32)) by { rewrite(at(vector_a, byte_vec[0]), (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0]); close(); }
       have to_integer(at(vector_a, val.0[0])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 0] as int32)) by close() using { to_integer(at(vector_a, val.0[0])) == at(vector_a, to_integer((byte_vec[0] as int32))); at(vector_a, to_integer((byte_vec[0] as int32))) == to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] as int32)); to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[0] as int32)) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 0] as int32)); };
       apply(adler_count_previous_chunk_byte_observation(bytes.as_ptr(), (bytes.len() - bytes.len() % 4u64), adler_chunk_bytes(iter.len()), 1));
       have at(vector_a, byte_vec[1]) == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] by close() using { byte_vec[1] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1]; };
       have at(vector_a, to_integer((byte_vec[1] as int32))) == to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] as int32)) by { rewrite(at(vector_a, byte_vec[1]), (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1]); close(); }
       have to_integer(at(vector_a, val.0[1])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) by close() using { to_integer(at(vector_a, val.0[1])) == at(vector_a, to_integer((byte_vec[1] as int32))); at(vector_a, to_integer((byte_vec[1] as int32))) == to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] as int32)); to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[1] as int32)) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)); };
       apply(adler_count_previous_chunk_byte_observation(bytes.as_ptr(), (bytes.len() - bytes.len() % 4u64), adler_chunk_bytes(iter.len()), 2));
       have at(vector_a, byte_vec[2]) == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] by close() using { byte_vec[2] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2]; };
       have at(vector_a, to_integer((byte_vec[2] as int32))) == to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] as int32)) by { rewrite(at(vector_a, byte_vec[2]), (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2]); close(); }
       have to_integer(at(vector_a, val.0[2])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) by close() using { to_integer(at(vector_a, val.0[2])) == at(vector_a, to_integer((byte_vec[2] as int32))); at(vector_a, to_integer((byte_vec[2] as int32))) == to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] as int32)); to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[2] as int32)) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)); };
       apply(adler_count_previous_chunk_byte_observation(bytes.as_ptr(), (bytes.len() - bytes.len() % 4u64), adler_chunk_bytes(iter.len()), 3));
       have at(vector_a, byte_vec[3]) == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] by close() using { byte_vec[3] == (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3]; };
       have at(vector_a, to_integer((byte_vec[3] as int32))) == to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] as int32)) by { rewrite(at(vector_a, byte_vec[3]), (bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3]); close(); }
       have to_integer(at(vector_a, val.0[3])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)) by close() using { to_integer(at(vector_a, val.0[3])) == at(vector_a, to_integer((byte_vec[3] as int32))); at(vector_a, to_integer((byte_vec[3] as int32))) == to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] as int32)); to_integer(((bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) - 4u64))[3] as int32)) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)); };
       have 0 <= to_integer((at(vector_a, a_vec.0[0])));
       have to_integer((at(vector_a, a_vec.0[0]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, b_vec.0[0])));
       have to_integer((at(vector_a, b_vec.0[0]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, val.0[0])));
       have to_integer((at(vector_a, val.0[0]))) <= 4294967295;
       have 0 <= to_integer(at(vector_a, a_vec.0[0]));
       have 0 <= to_integer(at(vector_a, b_vec.0[0]));
       have to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have 0 <= to_integer(at(vector_a, val.0[0]));
       have to_integer(at(vector_a, val.0[0])) <= 255;
       apply(adler_lane_iterator_add_contracts(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, val.0[0])));
       apply(adler_lane_iterator_native_preservation(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, val.0[0])));
       have 0 <= to_integer((at(vector_a, a_vec.0[1])));
       have to_integer((at(vector_a, a_vec.0[1]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, b_vec.0[1])));
       have to_integer((at(vector_a, b_vec.0[1]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, val.0[1])));
       have to_integer((at(vector_a, val.0[1]))) <= 4294967295;
       have 0 <= to_integer(at(vector_a, a_vec.0[1]));
       have 0 <= to_integer(at(vector_a, b_vec.0[1]));
       have to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have 0 <= to_integer(at(vector_a, val.0[1]));
       have to_integer(at(vector_a, val.0[1])) <= 255;
       apply(adler_lane_iterator_add_contracts(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, val.0[1])));
       apply(adler_lane_iterator_native_preservation(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, val.0[1])));
       have 0 <= to_integer((at(vector_a, a_vec.0[2])));
       have to_integer((at(vector_a, a_vec.0[2]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, b_vec.0[2])));
       have to_integer((at(vector_a, b_vec.0[2]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, val.0[2])));
       have to_integer((at(vector_a, val.0[2]))) <= 4294967295;
       have 0 <= to_integer(at(vector_a, a_vec.0[2]));
       have 0 <= to_integer(at(vector_a, b_vec.0[2]));
       have to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have 0 <= to_integer(at(vector_a, val.0[2]));
       have to_integer(at(vector_a, val.0[2])) <= 255;
       apply(adler_lane_iterator_add_contracts(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, val.0[2])));
       apply(adler_lane_iterator_native_preservation(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, val.0[2])));
       have 0 <= to_integer((at(vector_a, a_vec.0[3])));
       have to_integer((at(vector_a, a_vec.0[3]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, b_vec.0[3])));
       have to_integer((at(vector_a, b_vec.0[3]))) <= 4294967295;
       have 0 <= to_integer((at(vector_a, val.0[3])));
       have to_integer((at(vector_a, val.0[3]))) <= 4294967295;
       have 0 <= to_integer(at(vector_a, a_vec.0[3]));
       have 0 <= to_integer(at(vector_a, b_vec.0[3]));
       have to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       have 0 <= to_integer(at(vector_a, val.0[3]));
       have to_integer(at(vector_a, val.0[3])) <= 255;
       apply(adler_lane_iterator_add_contracts(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[3])));
       apply(adler_lane_iterator_native_preservation(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, val.0[3])));
       step_until(loop(2).statement(2).entry);
       have a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]);
       have b_vec.0[0] == at(vector_a, b_vec.0[0]);
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])) by close() using { b_vec.0[0] == at(vector_a, b_vec.0[0]); };
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) by {
        apply(adler_stored_sum(a_vec.0[0], at(vector_a, a_vec.0[0]), at(vector_a, val.0[0])));
       }
       have to_integer(b_vec.0[0]) + to_integer(a_vec.0[0]) <= 4294967295 by {
        apply(integer::equal_add(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0])), to_integer(a_vec.0[0]), to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))));
        apply(integer::le_substitute(to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])), 4294967295, to_integer(b_vec.0[0]) + to_integer(a_vec.0[0]), 4294967295));
       }
       have a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]);
       have b_vec.0[1] == at(vector_a, b_vec.0[1]);
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])) by close() using { b_vec.0[1] == at(vector_a, b_vec.0[1]); };
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) by {
        apply(adler_stored_sum(a_vec.0[1], at(vector_a, a_vec.0[1]), at(vector_a, val.0[1])));
       }
       have to_integer(b_vec.0[1]) + to_integer(a_vec.0[1]) <= 4294967295 by {
        apply(integer::equal_add(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1])), to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))));
        apply(integer::le_substitute(to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])), 4294967295, to_integer(b_vec.0[1]) + to_integer(a_vec.0[1]), 4294967295));
       }
       have a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]);
       have b_vec.0[2] == at(vector_a, b_vec.0[2]);
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])) by close() using { b_vec.0[2] == at(vector_a, b_vec.0[2]); };
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) by {
        apply(adler_stored_sum(a_vec.0[2], at(vector_a, a_vec.0[2]), at(vector_a, val.0[2])));
       }
       have to_integer(b_vec.0[2]) + to_integer(a_vec.0[2]) <= 4294967295 by {
        apply(integer::equal_add(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2])), to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))));
        apply(integer::le_substitute(to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])), 4294967295, to_integer(b_vec.0[2]) + to_integer(a_vec.0[2]), 4294967295));
       }
       have a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]);
       have b_vec.0[3] == at(vector_a, b_vec.0[3]);
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])) by close() using { b_vec.0[3] == at(vector_a, b_vec.0[3]); };
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) by {
        apply(adler_stored_sum(a_vec.0[3], at(vector_a, a_vec.0[3]), at(vector_a, val.0[3])));
       }
       have to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]) <= 4294967295 by {
        apply(integer::equal_add(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3])), to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))));
        apply(integer::le_substitute(to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])), 4294967295, to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]), 4294967295));
       }
       mark vector_b;
       step_until(loop.back_edge);
       have a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]);
       have b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]));
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) by {
        apply(adler_stored_sum(a_vec.0[0], at(vector_a, a_vec.0[0]), at(vector_a, val.0[0])));
       }
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by {
        rewrite(((adler_chunk_bytes(iter.len()) as uint32) as int32), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4);
        close();
       }
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by {
        apply(integer::le_substitute(to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])), adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer(a_vec.0[0]), adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)))));
       }
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))) by {
        apply(adler_stored_sum(b_vec.0[0], at(vector_a, b_vec.0[0]), (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))));
       }
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by {
        rewrite(((adler_chunk_bytes(iter.len()) as uint32) as int32), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4);
        close();
       }
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by {
        apply(integer::le_substitute(to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))), adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer(b_vec.0[0]), adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)))));
       }
       have a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]);
       have b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]));
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) by {
        apply(adler_stored_sum(a_vec.0[1], at(vector_a, a_vec.0[1]), at(vector_a, val.0[1])));
       }
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by {
        apply(integer::le_substitute(to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])), adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer(a_vec.0[1]), adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)))));
       }
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))) by {
        apply(adler_stored_sum(b_vec.0[1], at(vector_a, b_vec.0[1]), (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))));
       }
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by {
        apply(integer::le_substitute(to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))), adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer(b_vec.0[1]), adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)))));
       }
       have a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]);
       have b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]));
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) by {
        apply(adler_stored_sum(a_vec.0[2], at(vector_a, a_vec.0[2]), at(vector_a, val.0[2])));
       }
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by {
        apply(integer::le_substitute(to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])), adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer(a_vec.0[2]), adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)))));
       }
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))) by {
        apply(adler_stored_sum(b_vec.0[2], at(vector_a, b_vec.0[2]), (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))));
       }
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by {
        apply(integer::le_substitute(to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))), adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer(b_vec.0[2]), adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)))));
       }
       have a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]);
       have b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]));
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) by {
        apply(adler_stored_sum(a_vec.0[3], at(vector_a, a_vec.0[3]), at(vector_a, val.0[3])));
       }
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by {
        apply(integer::le_substitute(to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])), adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer(a_vec.0[3]), adler_lane_a_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)))));
       }
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))) by {
        apply(adler_stored_sum(b_vec.0[3], at(vector_a, b_vec.0[3]), (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))));
       }
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by {
        apply(integer::le_substitute(to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))), adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer(b_vec.0[3]), adler_lane_b_ceiling(adler_lane_vectors_consumed(old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), ((adler_chunk_bytes(iter.len()) as uint32) as int32)))));
       }
       have 0 <= ((adler_chunk_bytes(iter.len()) as uint32) as int32) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); };
       have ((adler_chunk_bytes(iter.len()) as uint32) as int32) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; };
       have 0 <= ((adler_chunk_bytes(iter.len()) as uint32) as int32) and ((adler_chunk_bytes(iter.len()) as uint32) as int32) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) by close();
       have to_integer(iter.len()) <= to_integer(at(lane_head, iter.len())) by close() using {
        to_integer(iter.len()) == to_integer(at(lane_head, iter.len())) - 1;
       };
       apply(integer::uint64_to_integer_less_equal_implies_less_equal(iter.len(), at(lane_head, iter.len())));
       apply(integer::uint64_less_equal_transitive(iter.len(), at(lane_head, iter.len()), 5551u64));
       apply(adler_chunk_bytes_value(iter.len()));
       have to_integer(((adler_chunk_bytes(iter.len()) as uint32) as int32)) == to_integer(iter.len()) * 4 by {
        rewrite(to_integer(((adler_chunk_bytes(iter.len()) as uint32) as int32)), to_integer(adler_chunk_bytes(iter.len())));
        close();
       }
       apply(adler_int32_multiple_of_four(((adler_chunk_bytes(iter.len()) as uint32) as int32), to_integer(iter.len())));
       have at(lane_head, adler_chunk_bytes(iter.len())) <= bytes.len() - bytes.len() % 4u64 by close();
       apply(integer::uint64_subtract_to_integer(at(lane_head, adler_chunk_bytes(iter.len())), 4u64));
       have to_integer(adler_chunk_bytes(iter.len())) == to_integer(at(lane_head, adler_chunk_bytes(iter.len()))) - 4 by {
        rewrite(adler_chunk_bytes(iter.len()), at(lane_head, adler_chunk_bytes(iter.len())) - 4u64);
        close();
       }
       have to_integer(at(lane_head, adler_chunk_bytes(iter.len()))) <= to_integer(bytes.len() - bytes.len() % 4u64) by close();
       have to_integer(adler_chunk_bytes(iter.len())) <= to_integer(bytes.len() - bytes.len() % 4u64) by {
        apply(integer::subtract_le(to_integer(at(lane_head, adler_chunk_bytes(iter.len()))), to_integer(bytes.len() - bytes.len() % 4u64), 4, 0));
        close();
       }
       apply(integer::uint64_to_integer_less_equal_implies_less_equal(adler_chunk_bytes(iter.len()), bytes.len() - bytes.len() % 4u64));
       apply(integer::uint64_subtract_to_integer(bytes.len() - bytes.len() % 4u64, at(lane_head, adler_chunk_bytes(iter.len()))));
       have to_integer(bytes.len() - bytes.len() % 4u64) <= 22207 by close();
       have to_integer((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) <= 22207 by {
        rewrite(to_integer((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))), to_integer(bytes.len() - bytes.len() % 4u64) - to_integer(at(lane_head, adler_chunk_bytes(iter.len()))));
        apply(integer::subtract_le(to_integer(bytes.len() - bytes.len() % 4u64), 22207, to_integer(at(lane_head, adler_chunk_bytes(iter.len()))), 0));
        close();
       }
       have to_integer((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) + 4 <= 18446744073709551615 by close();
       apply(integer::uint64_add_to_integer((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())), 4u64));
       apply(integer::uint64_subtract_to_integer(bytes.len() - bytes.len() % 4u64, adler_chunk_bytes(iter.len())));
       have (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) == ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) + 4u64 by {
        have to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len())) == to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) + 4u64) by {
         rewrite(to_integer((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len())), to_integer(bytes.len() - bytes.len() % 4u64) - to_integer(adler_chunk_bytes(iter.len())));
         rewrite(to_integer(adler_chunk_bytes(iter.len())), to_integer(at(lane_head, adler_chunk_bytes(iter.len()))) - 4);
         rewrite(to_integer(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) + 4u64), to_integer((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) + 4);
         rewrite(to_integer((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))), to_integer(bytes.len() - bytes.len() % 4u64) - to_integer(at(lane_head, adler_chunk_bytes(iter.len()))));
         close();
        }
        close();
       }
       have adler_chunk_bytes(iter.len()) % 4u64 == 0u64 by {
        apply(integer::uint64_remainder_to_integer(adler_chunk_bytes(iter.len()), 4u64));
        apply(adler_multiple_of_four(to_integer(iter.len())));
        have to_integer(adler_chunk_bytes(iter.len()) % 4u64) == 0 by {
         rewrite(to_integer(adler_chunk_bytes(iter.len()) % 4u64), truncating_remainder(to_integer(adler_chunk_bytes(iter.len())), 4));
         rewrite(to_integer(adler_chunk_bytes(iter.len())), to_integer(iter.len()) * 4);
         close();
        }
        close();
       }
       have adler_chunk_bytes(iter.len()) < at(lane_head, adler_chunk_bytes(iter.len())) by close() using { adler_chunk_bytes(iter.len()) == at(lane_head, adler_chunk_bytes(iter.len())) - 4u64; 4u64 <= at(lane_head, adler_chunk_bytes(iter.len())); };
       have ((adler_chunk_bytes(iter.len()) as uint32) as int32) < at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; };
       have (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have 0 <= (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) by close() using { (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) <= 2147483643 by close() using { (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have to_integer(a) == at(lane_head, to_integer(a)) by close();
       have (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) == prefix_model_count by close();
       have 0 <= prefix_model_count by close();
       have forall (k: int32) { 0 <= k and k < prefix_model_count implies bytes[k] == at(lane_head, bytes[k]) } by {
        intro() {
         intro() {
          have at(region(292).entry, bytes[k]) == at(lane_head, bytes[k]) by close();
          have separate(region(292).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(292).exit, bytes[k]) == at(region(292).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(292)); }
          have at(region(292).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(292).exit, bytes[k]) == at(region(292).entry, bytes[k]);
           at(region(292).entry, bytes[k]) == at(lane_head, bytes[k]);
           at(lane_head, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(293).entry, bytes[k]) == at(region(292).exit, bytes[k]) by close();
          have separate(region(293).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(293).exit, bytes[k]) == at(region(293).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(293)); }
          have at(region(293).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(293).exit, bytes[k]) == at(region(293).entry, bytes[k]);
           at(region(293).entry, bytes[k]) == at(region(292).exit, bytes[k]);
           at(region(292).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(301).entry, bytes[k]) == at(region(293).exit, bytes[k]) by close();
          have separate(region(301).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(301).exit, bytes[k]) == at(region(301).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(301)); }
          have at(region(301).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(301).exit, bytes[k]) == at(region(301).entry, bytes[k]);
           at(region(301).entry, bytes[k]) == at(region(293).exit, bytes[k]);
           at(region(293).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(307).entry, bytes[k]) == at(region(301).exit, bytes[k]) by close();
          have separate(region(307).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(307).exit, bytes[k]) == at(region(307).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(307)); }
          have at(region(307).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(307).exit, bytes[k]) == at(region(307).entry, bytes[k]);
           at(region(307).entry, bytes[k]) == at(region(301).exit, bytes[k]);
           at(region(301).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(316).entry, bytes[k]) == at(region(307).exit, bytes[k]) by close();
          have separate(region(316).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(316).exit, bytes[k]) == at(region(316).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(316)); }
          have at(region(316).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(316).exit, bytes[k]) == at(region(316).entry, bytes[k]);
           at(region(316).entry, bytes[k]) == at(region(307).exit, bytes[k]);
           at(region(307).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(318).entry, bytes[k]) == at(region(316).exit, bytes[k]) by close();
          have separate(region(318).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(318).exit, bytes[k]) == at(region(318).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(318)); }
          have at(region(318).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(318).exit, bytes[k]) == at(region(318).entry, bytes[k]);
           at(region(318).entry, bytes[k]) == at(region(316).exit, bytes[k]);
           at(region(316).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(319).entry, bytes[k]) == at(region(318).exit, bytes[k]) by close();
          have separate(region(319).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(319).exit, bytes[k]) == at(region(319).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(319)); }
          have at(region(319).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(319).exit, bytes[k]) == at(region(319).entry, bytes[k]);
           at(region(319).entry, bytes[k]) == at(region(318).exit, bytes[k]);
           at(region(318).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(327).entry, bytes[k]) == at(region(319).exit, bytes[k]) by close();
          have separate(region(327).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(327).exit, bytes[k]) == at(region(327).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(327)); }
          have at(region(327).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(327).exit, bytes[k]) == at(region(327).entry, bytes[k]);
           at(region(327).entry, bytes[k]) == at(region(319).exit, bytes[k]);
           at(region(319).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(329).entry, bytes[k]) == at(region(327).exit, bytes[k]) by close();
          have separate(region(329).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(329).exit, bytes[k]) == at(region(329).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(329)); }
          have at(region(329).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(329).exit, bytes[k]) == at(region(329).entry, bytes[k]);
           at(region(329).entry, bytes[k]) == at(region(327).exit, bytes[k]);
           at(region(327).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(330).entry, bytes[k]) == at(region(329).exit, bytes[k]) by close();
          have separate(region(330).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(330).exit, bytes[k]) == at(region(330).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(330)); }
          have at(region(330).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(330).exit, bytes[k]) == at(region(330).entry, bytes[k]);
           at(region(330).entry, bytes[k]) == at(region(329).exit, bytes[k]);
           at(region(329).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(334).entry, bytes[k]) == at(region(330).exit, bytes[k]) by close();
          have separate(region(334).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(334).exit, bytes[k]) == at(region(334).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(334)); }
          have at(region(334).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(334).exit, bytes[k]) == at(region(334).entry, bytes[k]);
           at(region(334).entry, bytes[k]) == at(region(330).exit, bytes[k]);
           at(region(330).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have at(region(335).entry, bytes[k]) == at(region(334).exit, bytes[k]) by close();
          have separate(region(335).footprint, at(lane_head, memory(bytes[k]))) by close();
          have at(region(335).exit, bytes[k]) == at(region(335).entry, bytes[k]) by { preserve(at(lane_head, memory(bytes[k])), region(335)); }
          have at(region(335).exit, bytes[k]) == at(lane_head, bytes[k]) by close() using {
           at(region(335).exit, bytes[k]) == at(region(335).entry, bytes[k]);
           at(region(335).entry, bytes[k]) == at(region(334).exit, bytes[k]);
           at(region(334).exit, bytes[k]) == at(lane_head, bytes[k]);
          };
          have bytes[k] == at(region(335).exit, bytes[k]) by close();
          close() using { bytes[k] == at(region(335).exit, bytes[k]); at(region(335).exit, bytes[k]) == at(lane_head, bytes[k]); };
         }
        }
       }
       have to_integer(b) == at(lane_head, to_integer(b)) by close();
       apply(adler_spec_extensional(bytes.as_ptr(), at(lane_head, bytes.as_ptr()), prefix_model_count, at(lane_head, to_integer(a)), at(lane_head, to_integer(b))));
       have adler_spec_a(bytes.as_ptr(), (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), at(lane_head, to_integer(a))) == at(lane_head, adler_spec_a(bytes.as_ptr(), prefix_model_count, to_integer(a))) by {
        rewrite((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), prefix_model_count);
        close();
       }
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), 65521) == adler_spec_a(bytes.as_ptr(), (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), to_integer(a)) by {  rewrite(at(vector_a, a_vec.0[0]), at(lane_head, a_vec.0[0])); rewrite(at(vector_a, a_vec.0[1]), at(lane_head, a_vec.0[1])); rewrite(at(vector_a, a_vec.0[2]), at(lane_head, a_vec.0[2])); rewrite(at(vector_a, a_vec.0[3]), at(lane_head, a_vec.0[3]));  rewrite(to_integer(a), at(lane_head, to_integer(a))); rewrite(adler_spec_a(bytes.as_ptr(), (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), at(lane_head, to_integer(a))), at(lane_head, adler_spec_a(bytes.as_ptr(), prefix_model_count, to_integer(a)))); close(); }
       have 0 <= to_integer(at(vector_a, a_vec.0[0])) by close();
       have 0 <= to_integer(at(vector_a, a_vec.0[1])) by close();
       have 0 <= to_integer(at(vector_a, a_vec.0[2])) by close();
       have 0 <= to_integer(at(vector_a, a_vec.0[3])) by close();
       have 0 <= adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) by {
        unfold(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))));
        close() using { 0 <= to_integer(a); 0 <= to_integer(at(vector_a, a_vec.0[0])); 0 <= to_integer(at(vector_a, a_vec.0[1])); 0 <= to_integer(at(vector_a, a_vec.0[2])); 0 <= to_integer(at(vector_a, a_vec.0[3])); };
       }
       have defined(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by close();
       have to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - to_integer(((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close();
       have defined((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close();
       have 0 <= to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close();
       have to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) == to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) - 4 by close();
       have to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) <= 2147483643 by close() using { to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) == to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) - 4; to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) == to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - to_integer(((adler_chunk_bytes(iter.len()) as uint32) as int32)); (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) <= 2147483643; };
       apply(adler_prefix_a_step_four(bytes.as_ptr(), (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), to_integer(a), adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])))));
       apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[0]), at(vector_a, val.0[0])));
       apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[1]), at(vector_a, val.0[1])));
       apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[2]), at(vector_a, val.0[2])));
       apply(integer::uint32_add_to_integer(at(vector_a, a_vec.0[3]), at(vector_a, val.0[3])));
       have defined((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 0) by close();
       have to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 0) == to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) by close();
       have to_integer(at(vector_a, val.0[0])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) by { rewrite(to_integer(at(vector_a, val.0[0])), to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 0] as int32))); close(); }
       have adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) == adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + (to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32))) by { unfold(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); unfold(adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])))); close() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])) == to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0])); to_integer(at(vector_a, val.0[0])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])) == to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])); to_integer(at(vector_a, val.0[1])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])) == to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])); to_integer(at(vector_a, val.0[2])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])) == to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3])); to_integer(at(vector_a, val.0[3])) == to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)); }; }
       have ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) == (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 4 by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes.as_ptr(), ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), to_integer(a)) by { rewrite(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + (to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)))); rewrite(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 4); close(); }
       have 0 <= to_integer(b);
       have to_integer(b) <= 4294967295;
       have to_integer(a) <= to_integer(65520u32);
       have to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) == to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))) by {
        apply(adler_same_signed_index((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32))));
       }
       have 0 <= adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) by { rewrite(to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)), to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)))); close(); }
       have adler_spec_b(bytes.as_ptr(), prefix_model_count, at(lane_head, to_integer(a)), at(lane_head, to_integer(b))) == at(lane_head, adler_spec_b(bytes.as_ptr(), prefix_model_count, to_integer(a), to_integer(b))) by close();
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))), 65521) == adler_spec_b(bytes.as_ptr(), (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), to_integer(a), to_integer(b)) by {
        rewrite((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), prefix_model_count);
        rewrite(to_integer(a), at(lane_head, to_integer(a)));
        rewrite(to_integer(b), at(lane_head, to_integer(b)));
        rewrite(at(vector_a, a_vec.0[1]), at(lane_head, a_vec.0[1]));
        rewrite(at(vector_a, a_vec.0[2]), at(lane_head, a_vec.0[2]));
        rewrite(at(vector_a, a_vec.0[3]), at(lane_head, a_vec.0[3]));
        rewrite(at(vector_a, b_vec.0[0]), at(lane_head, b_vec.0[0]));
        rewrite(at(vector_a, b_vec.0[1]), at(lane_head, b_vec.0[1]));
        rewrite(at(vector_a, b_vec.0[2]), at(lane_head, b_vec.0[2]));
        rewrite(at(vector_a, b_vec.0[3]), at(lane_head, b_vec.0[3]));
        rewrite(adler_spec_b(bytes.as_ptr(), prefix_model_count, at(lane_head, to_integer(a)), at(lane_head, to_integer(b))), at(lane_head, adler_spec_b(bytes.as_ptr(), prefix_model_count, to_integer(a), to_integer(b))));
        close();
       }
       apply(adler_prefix_b_step_four(bytes.as_ptr(), (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4), to_integer(a), to_integer(b), adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))), adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3])))));
       have (((bytes.len() - bytes.len() % 4u64) as u32) as i32) <= 22204 by close() using { (((bytes.len() - bytes.len() % 4u64) as u32) as i32) == old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)); old((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) <= 22204; };
       have 4 <= ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close() using { ((adler_chunk_bytes(iter.len()) as uint32) as int32) == at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4; 4 <= at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)); at(lane_head, ((adler_chunk_bytes(iter.len()) as uint32) as int32)) <= old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) <= 22204; (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == old((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)); };
       have 4 <= to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) by close() using { to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) == to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - to_integer(((adler_chunk_bytes(iter.len()) as uint32) as int32)); 4 <= ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)); };
       apply(adler_small_prefix_integer_advance((((bytes.len() - bytes.len() % 4u64) as uint32) as int32), ((adler_chunk_bytes(iter.len()) as uint32) as int32)));
       have to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a) == (to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a)) + 4 * to_integer(a) by { rewrite(to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))), to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) + 4); close() using {  }; }
       apply(integer::uint32_add_to_integer(at(vector_a, b_vec.0[0]), at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])));
       apply(integer::uint32_add_to_integer(at(vector_a, b_vec.0[1]), at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
       apply(integer::uint32_add_to_integer(at(vector_a, b_vec.0[2]), at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
       apply(integer::uint32_add_to_integer(at(vector_a, b_vec.0[3]), at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0])) by {
        rewrite(to_integer(a_vec.0[0]), to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])));
        close();
       }
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0])) by {
        rewrite(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))));
        rewrite(to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0]))), to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])));
        rewrite(to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, val.0[0])), to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0])));
        close() using {};
       }
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])) by {
        rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
        close();
       }
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])) by {
        rewrite(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))));
        rewrite(to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1]))), to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])));
        rewrite(to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, val.0[1])), to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])));
        close() using {};
       }
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])) by {
        rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
        close();
       }
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])) by {
        rewrite(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))));
        rewrite(to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2]))), to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])));
        rewrite(to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, val.0[2])), to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])));
        close() using {};
       }
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3])) by {
        rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
        close();
       }
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3])) by {
        rewrite(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))));
        rewrite(to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3]))), to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])));
        rewrite(to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, val.0[3])), to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3])));
        close() using {};
       }
       apply(adler_four_lane_state_step(to_integer(a), to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3])), to_integer(at(vector_a, val.0[0])), to_integer(at(vector_a, val.0[1])), to_integer(at(vector_a, val.0[2])), to_integer(at(vector_a, val.0[3]))));
       have adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) == (adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)))) by {
        rewrite(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), (to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a)) + 4 * to_integer(a));
        rewrite(to_integer(a_vec.0[1]), to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])));
        rewrite(to_integer(a_vec.0[2]), to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])));
        rewrite(to_integer(a_vec.0[3]), to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3])));
        rewrite(to_integer(b_vec.0[0]), to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0])));
        rewrite(to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)), to_integer(at(vector_a, val.0[0])));
        rewrite(to_integer(b_vec.0[1]), to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])));
        rewrite(to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)), to_integer(at(vector_a, val.0[1])));
        rewrite(to_integer(b_vec.0[2]), to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])));
        rewrite(to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)), to_integer(at(vector_a, val.0[2])));
        rewrite(to_integer(b_vec.0[3]), to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3])));
        rewrite(to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)), to_integer(at(vector_a, val.0[3])));
        close() using { adler_lane_b((to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a)) + 4 * to_integer(a), to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])), to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])), to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3])), to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0])) + to_integer(at(vector_a, val.0[0])), to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1])) + to_integer(at(vector_a, val.0[1])), to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2])) + to_integer(at(vector_a, val.0[2])), to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3])) + to_integer(at(vector_a, val.0[3]))) == adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + 4 * to_integer(at(vector_a, val.0[0])) + 3 * to_integer(at(vector_a, val.0[1])) + 2 * to_integer(at(vector_a, val.0[2])) + to_integer(at(vector_a, val.0[3])); };
       }
       have truncating_remainder(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes.as_ptr(), ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), to_integer(a), to_integer(b)) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), (adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32))))); rewrite(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)), (((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 4); close(); }
       apply(adler_byte_bounds(bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)]));
       apply(adler_byte_bounds(bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1]));
       apply(adler_byte_bounds(bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2]));
       apply(adler_byte_bounds(bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3]));
       have 0 <= adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) by close() using { 0 <= adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))); 0 <= adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))); };
       have 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32))) by {
        apply(integer::multiply_order_nonnegative(0, to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)), 4));
        apply(integer::multiply_commutative(to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)), 4));
        have 0 * 4 == 0 by close();
        apply(integer::le_substitute(0 * 4, to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) * 4, 0, 4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32))));
       }
       have 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32))) by close() using { 0 <= to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)); 0 <= to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)); };
       have 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32))) by close() using { 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32))); 0 <= to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)); };
       have 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32))) by close() using { 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32))); 0 <= to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32)); };
       have 0 <= adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), (adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))) + (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32))))); close() using { 0 <= adler_lane_b(to_integer(b) + to_integer((((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)) * to_integer(a), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3])), to_integer(at(vector_a, b_vec.0[0])), to_integer(at(vector_a, b_vec.0[1])), to_integer(at(vector_a, b_vec.0[2])), to_integer(at(vector_a, b_vec.0[3]))) + 4 * adler_lane_a(to_integer(a), to_integer(at(vector_a, a_vec.0[0])), to_integer(at(vector_a, a_vec.0[1])), to_integer(at(vector_a, a_vec.0[2])), to_integer(at(vector_a, a_vec.0[3]))); 0 <= (4 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4)] as int32)) + 3 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 1] as int32)) + 2 * to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 2] as int32)) + to_integer((bytes[(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(iter.len()) as uint32) as int32)) - 4) + 3] as int32))); }; }
       have defined(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) - (((adler_chunk_bytes(iter.len()) as uint32) as int32)));
       have loop(2).iter.v == byte_offset(at(lane_head, loop(2).iter.v), 4) by close();
       have iter.len() == at(lane_head, iter.len()) - 1u64;
       have 0u64 < at(lane_head, iter.len());
       have iter.len() < at(lane_head, iter.len());
       have exists (offset: uint64) { offset == ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) } by { witness(((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len())))); close(); }
       let prior_offset = obtain(exists (offset: uint64) { offset == ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))) });
       have at(lane_head, loop(2).iter.v) == bytes.as_ptr() + prior_offset by {
        rewrite(prior_offset, ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))));
        close();
       }
       have to_integer(prior_offset) <= 22207 by {
        rewrite(prior_offset, ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))));
        close();
       }
       have to_integer(prior_offset) + 4 <= 18446744073709551615 by close();
       have (bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len()) == prior_offset + 4u64 by {
        rewrite(prior_offset, ((bytes.len() - bytes.len() % 4u64) - at(lane_head, adler_chunk_bytes(iter.len()))));
        close();
       }
       have byte_offset(bytes.as_ptr() + prior_offset, 4) == (bytes.as_ptr() + prior_offset) + 4u64 by close() using {};
       apply(adler_uint64_pointer_association(bytes.as_ptr(), prior_offset, 4u64));
       have iter.v == bytes.as_ptr() + ((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len())) by {
        rewrite(loop(2).iter.v, byte_offset(at(lane_head, loop(2).iter.v), 4));
        rewrite(at(lane_head, loop(2).iter.v), bytes.as_ptr() + prior_offset);
        rewrite(byte_offset(bytes.as_ptr() + prior_offset, 4), (bytes.as_ptr() + prior_offset) + 4u64);
        rewrite((bytes.as_ptr() + prior_offset) + 4u64, bytes.as_ptr() + (prior_offset + 4u64));
        rewrite(((bytes.len() - bytes.len() % 4u64) - adler_chunk_bytes(iter.len())), prior_offset + 4u64);
        close();
       }
       have iter.chunk_size == 4u64 by close();
       have to_integer(iter.len()) + (iterations + 1) == to_integer((bytes.len() - bytes.len() % 4u64) / 4u64) by close() using { to_integer(iter.len()) == to_integer(at(lane_head, iter.len())) - 1; at(lane_head, to_integer(iter.len())) + iterations == to_integer((bytes.len() - bytes.len() % 4u64) / 4u64); };
      }
     }
     have loop(2).iter.len() == 0u64;
     have adler_chunk_bytes(loop(2).iter.len()) == 0u64 by { rewrite(loop(2).iter.len(), 0u64); apply(adler_chunk_bytes_zero()); close(); }
     have ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) == 0 by { rewrite(adler_chunk_bytes(loop(2).iter.len()), 0u64); close(); }
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == adler_spec_a(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(a)) by {
      have (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), 0); close(); }
      rewrite((((bytes.len() - bytes.len() % 4u64) as uint32) as int32), (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32));
      close();
     }
     have truncating_remainder(adler_lane_b(to_integer(b) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == adler_spec_b(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(a), to_integer(b)) by {
      have (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32) by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), 0); close(); }
      have to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) == to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by close() using { (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32); };
      have adler_lane_b(to_integer(b) + to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) == adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by { rewrite(to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)))); close(); }
      have adler_spec_b(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as uint32) as int32), to_integer(a), to_integer(b)) == adler_spec_b(bytes.as_ptr(), ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), to_integer(a), to_integer(b)) by close() using { (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32); };
      rewrite(adler_lane_b(to_integer(b) + to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), adler_lane_b(to_integer(b) + to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])));
      rewrite(adler_spec_b(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as uint32) as int32), to_integer(a), to_integer(b)), adler_spec_b(bytes.as_ptr(), ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)), to_integer(a), to_integer(b)));
      close();
     }
     have 0 <= adler_lane_b(to_integer(b) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(a), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])) by {
      have (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)) by { rewrite(((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32), 0); close(); }
      have to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)) == to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32))) by close() using { (((bytes.len() - bytes.len() % 4u64) as uint32) as int32) == ((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)); };
      rewrite(to_integer((((bytes.len() - bytes.len() % 4u64) as uint32) as int32)), to_integer(((((bytes.len() - bytes.len() % 4u64) as uint32) as int32) - ((adler_chunk_bytes(loop(2).iter.len()) as uint32) as int32)))); close();
     }
     mark vector_prefix;
     have forall (k: int32) { 0 <= k and k < ((backing_length as u32) as i32) implies bytes[k] == old(bytes[k]) } by close();
     have forall (k: int32) { 0 <= k and k < ((backing_length as u32) as i32) implies at(vector_prefix, bytes[k]) == old(bytes[k]) } by close();
     have truncating_remainder(adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[3]))), 65521) == at(vector_prefix, adler_spec_b(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b))));
     have 0 <= adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[3])));
     have truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[0])), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3]))), 65521) == at(vector_prefix, adler_spec_a(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a))));
     have 0 <= to_integer((at(vector_prefix, a)));
     have to_integer((at(vector_prefix, a))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, a_vec.0[0])));
     have to_integer((at(vector_prefix, a_vec.0[0]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, a_vec.0[1])));
     have to_integer((at(vector_prefix, a_vec.0[1]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, a_vec.0[2])));
     have to_integer((at(vector_prefix, a_vec.0[2]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, a_vec.0[3])));
     have to_integer((at(vector_prefix, a_vec.0[3]))) <= 4294967295;
     apply(adler_lane_a_reduction(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[0])), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3]))));
     have remainder.len() == old(bytes.len()) % 4u64 by close();
     step_until(statement(11).entry);
     have remainder_chunk.len() == bytes.len() - bytes.len() % 4u64 by close();
     apply(adler_small_length_cast(bytes.len() - bytes.len() % 4u64));
     have (remainder_chunk.len() as u32) <= 22204u32 by {
      rewrite(remainder_chunk.len(), bytes.len() - bytes.len() % 4u64);
      close();
     }
     have a <= 65520u32 by close();
     apply(adler_scalar_batch_product_bound((remainder_chunk.len() as u32), a));
     have to_integer((remainder_chunk.len() as u32)) * to_integer(a) <= 4294967295 by close();
     apply(integer::uint32_multiply_guard_by_integer_bound((remainder_chunk.len() as u32), a));
     apply(integer::uint32_multiply_to_integer((remainder_chunk.len() as u32), a));
     apply(adler_count_observation(bytes.len() - bytes.len() % 4u64));
     have to_integer((remainder_chunk.len() as u32)) == to_integer(((bytes.len() - bytes.len() % 4u64) as u32 as i32)) by {
      rewrite(remainder_chunk.len(), bytes.len() - bytes.len() % 4u64);
      close();
     }
     have to_integer(((remainder_chunk.len() as u32) * a)) <= 1454806080 by close();
     have b <= 65520u32 by close();
     have to_integer(b) + to_integer(((remainder_chunk.len() as u32) * a)) <= 4294967295 by close() using {
      to_integer(b) <= 65520;
      to_integer(((remainder_chunk.len() as u32) * a)) <= 1454806080;
     };
     apply(integer::uint32_add_to_integer(b, ((remainder_chunk.len() as u32) * a)));
     mark deferred_b;
     have to_integer(at(deferred_b, b)) == to_integer(at(vector_prefix, b)) by close();
     have to_integer(at(deferred_b, ((remainder_chunk.len() as u32) * a))) == to_integer(((bytes.len() - bytes.len() % 4u64) as u32 as i32)) * to_integer(at(vector_prefix, a)) by close();
     if a == 0u32 {
      step_until(statement(12).entry);
     } else {
      step_until(statement(12).entry);
     }
     mark reduction_a;
     have to_integer(at(reduction_a, a_vec.0[0])) == to_integer(at(vector_prefix, a_vec.0[0]));
     have to_integer(at(reduction_a, a_vec.0[1])) == to_integer(at(vector_prefix, a_vec.0[1]));
     have to_integer(at(reduction_a, a_vec.0[2])) == to_integer(at(vector_prefix, a_vec.0[2]));
     have to_integer(at(reduction_a, a_vec.0[3])) == to_integer(at(vector_prefix, a_vec.0[3]));
     step_until(statement(13).entry);
     mark reduction_b;
     have to_integer(at(reduction_b, b_vec.0[0])) == to_integer(at(vector_prefix, b_vec.0[0]));
     have to_integer(at(reduction_b, b_vec.0[1])) == to_integer(at(vector_prefix, b_vec.0[1]));
     have to_integer(at(reduction_b, b_vec.0[2])) == to_integer(at(vector_prefix, b_vec.0[2]));
     have to_integer(at(reduction_b, b_vec.0[3])) == to_integer(at(vector_prefix, b_vec.0[3]));
     step_until(statement(14).entry);
     mark before_scalar_mod;
     have at(before_scalar_mod, b) == at(deferred_b, b) + at(deferred_b, ((remainder_chunk.len() as u32) * a));
     have to_integer(at(before_scalar_mod, b)) == to_integer(at(deferred_b, b) + at(deferred_b, ((remainder_chunk.len() as u32) * a))) by close() using { at(before_scalar_mod, b) == at(deferred_b, b) + at(deferred_b, ((remainder_chunk.len() as u32) * a)); };
     have to_integer(at(before_scalar_mod, b)) == to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)) by {
      rewrite(to_integer(at(before_scalar_mod, b)), to_integer(at(deferred_b, b) + at(deferred_b, ((remainder_chunk.len() as u32) * a))));
      rewrite(to_integer(at(deferred_b, b) + at(deferred_b, ((remainder_chunk.len() as u32) * a))), to_integer(at(deferred_b, b)) + to_integer(at(deferred_b, ((remainder_chunk.len() as u32) * a))));
      apply(integer::equal_add(to_integer(at(deferred_b, b)), to_integer(at(vector_prefix, b)), to_integer(at(deferred_b, ((remainder_chunk.len() as u32) * a))), to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a))));
     }

     have 0 <= to_integer(at(before_scalar_mod, b));
     have to_integer(at(before_scalar_mod, b)) <= 4294967295;
     have 0 <= to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)) by close() using { 0 <= to_integer(at(before_scalar_mod, b)); to_integer(at(before_scalar_mod, b)) == to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)); };
     have 0 <= to_integer((at(vector_prefix, b_vec.0[0])));
     have to_integer((at(vector_prefix, b_vec.0[0]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, b_vec.0[1])));
     have to_integer((at(vector_prefix, b_vec.0[1]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, b_vec.0[2])));
     have to_integer((at(vector_prefix, b_vec.0[2]))) <= 4294967295;
     have 0 <= to_integer((at(vector_prefix, b_vec.0[3])));
     have to_integer((at(vector_prefix, b_vec.0[3]))) <= 4294967295;
     apply(adler_lane_b_reduction(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[3]))));
     have statement(13).call(0).result == 65521u32;
     have 65521u32 == statement(13).call(0).result by close() using { statement(13).call(0).result == 65521u32; };
     have b_vec.0[0] < statement(13).call(0).result;
     have b_vec.0[0] < 65521u32 by { rewrite(65521u32, statement(13).call(0).result); close(); }
     have b_vec.0[0] <= 4294967295u32 / 4u32 by {
      have to_integer(b_vec.0[0]) <= to_integer(65521u32);
      have to_integer(65521u32) <= to_integer(4294967295u32 / 4u32) by close();
      apply(integer::le_transitive(to_integer(b_vec.0[0]), to_integer(65521u32), to_integer(4294967295u32 / 4u32)));
      apply(integer::uint32_to_integer_less_equal_implies_less_equal(b_vec.0[0], 4294967295u32 / 4u32));
     }
     have b_vec.0[1] < statement(13).call(0).result;
     have b_vec.0[1] < 65521u32 by { rewrite(65521u32, statement(13).call(0).result); close(); }
     have b_vec.0[1] <= 4294967295u32 / 4u32 by {
      have to_integer(b_vec.0[1]) <= to_integer(65521u32);
      have to_integer(65521u32) <= to_integer(4294967295u32 / 4u32) by close();
      apply(integer::le_transitive(to_integer(b_vec.0[1]), to_integer(65521u32), to_integer(4294967295u32 / 4u32)));
      apply(integer::uint32_to_integer_less_equal_implies_less_equal(b_vec.0[1], 4294967295u32 / 4u32));
     }
     have b_vec.0[2] < statement(13).call(0).result;
     have b_vec.0[2] < 65521u32 by { rewrite(65521u32, statement(13).call(0).result); close(); }
     have b_vec.0[2] <= 4294967295u32 / 4u32 by {
      have to_integer(b_vec.0[2]) <= to_integer(65521u32);
      have to_integer(65521u32) <= to_integer(4294967295u32 / 4u32) by close();
      apply(integer::le_transitive(to_integer(b_vec.0[2]), to_integer(65521u32), to_integer(4294967295u32 / 4u32)));
      apply(integer::uint32_to_integer_less_equal_implies_less_equal(b_vec.0[2], 4294967295u32 / 4u32));
     }
     have b_vec.0[3] < statement(13).call(0).result;
     have b_vec.0[3] < 65521u32 by { rewrite(65521u32, statement(13).call(0).result); close(); }
     have b_vec.0[3] <= 4294967295u32 / 4u32 by {
      have to_integer(b_vec.0[3]) <= to_integer(65521u32);
      have to_integer(65521u32) <= to_integer(4294967295u32 / 4u32) by close();
      apply(integer::le_transitive(to_integer(b_vec.0[3]), to_integer(65521u32), to_integer(4294967295u32 / 4u32)));
      apply(integer::uint32_to_integer_less_equal_implies_less_equal(b_vec.0[3], 4294967295u32 / 4u32));
     }
     have to_integer((b_vec.0[0])) < to_integer(65521u32);
     have to_integer(b_vec.0[0]) <= 65520 by close() using { to_integer(b_vec.0[0]) < 65521; };
     have to_integer((b_vec.0[1])) < to_integer(65521u32);
     have to_integer(b_vec.0[1]) <= 65520 by close() using { to_integer(b_vec.0[1]) < 65521; };
     have to_integer((b_vec.0[2])) < to_integer(65521u32);
     have to_integer(b_vec.0[2]) <= 65520 by close() using { to_integer(b_vec.0[2]) < 65521; };
     have to_integer((b_vec.0[3])) < to_integer(65521u32);
     have to_integer(b_vec.0[3]) <= 65520 by close() using { to_integer(b_vec.0[3]) < 65521; };
     have to_integer(a) == to_integer(at(vector_prefix, a));
     have statement(12).call(0).result == 65521u32;
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % statement(12).call(0).result;
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32 by { rewrite(a_vec.0[0], at(reduction_a, a_vec.0[0]) % statement(12).call(0).result); close() using { statement(12).call(0).result == 65521u32; }; }
     have to_integer((at(reduction_a, a_vec.0[0])) % 65521u32) == truncating_remainder(to_integer((at(reduction_a, a_vec.0[0]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_a, a_vec.0[0])), 65521u32)); }
     have to_integer(a_vec.0[0]) == to_integer(at(reduction_a, a_vec.0[0]) % 65521u32) by close() using { a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[0])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[0])), to_integer(at(vector_prefix, a_vec.0[0]))); close(); }
     have to_integer(a_vec.0[0]) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[0])), 65521) by close() using { to_integer(a_vec.0[0]) == to_integer(at(reduction_a, a_vec.0[0]) % 65521u32); to_integer(at(reduction_a, a_vec.0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[0])), 65521); };
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % statement(12).call(0).result;
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32 by { rewrite(a_vec.0[1], at(reduction_a, a_vec.0[1]) % statement(12).call(0).result); close() using { statement(12).call(0).result == 65521u32; }; }
     have to_integer((at(reduction_a, a_vec.0[1])) % 65521u32) == truncating_remainder(to_integer((at(reduction_a, a_vec.0[1]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_a, a_vec.0[1])), 65521u32)); }
     have to_integer(a_vec.0[1]) == to_integer(at(reduction_a, a_vec.0[1]) % 65521u32) by close() using { a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[1]))); close(); }
     have to_integer(a_vec.0[1]) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521) by close() using { to_integer(a_vec.0[1]) == to_integer(at(reduction_a, a_vec.0[1]) % 65521u32); to_integer(at(reduction_a, a_vec.0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521); };
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % statement(12).call(0).result;
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32 by { rewrite(a_vec.0[2], at(reduction_a, a_vec.0[2]) % statement(12).call(0).result); close() using { statement(12).call(0).result == 65521u32; }; }
     have to_integer((at(reduction_a, a_vec.0[2])) % 65521u32) == truncating_remainder(to_integer((at(reduction_a, a_vec.0[2]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_a, a_vec.0[2])), 65521u32)); }
     have to_integer(a_vec.0[2]) == to_integer(at(reduction_a, a_vec.0[2]) % 65521u32) by close() using { a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[2]))); close(); }
     have to_integer(a_vec.0[2]) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521) by close() using { to_integer(a_vec.0[2]) == to_integer(at(reduction_a, a_vec.0[2]) % 65521u32); to_integer(at(reduction_a, a_vec.0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521); };
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % statement(12).call(0).result;
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32 by { rewrite(a_vec.0[3], at(reduction_a, a_vec.0[3]) % statement(12).call(0).result); close() using { statement(12).call(0).result == 65521u32; }; }
     have to_integer((at(reduction_a, a_vec.0[3])) % 65521u32) == truncating_remainder(to_integer((at(reduction_a, a_vec.0[3]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_a, a_vec.0[3])), 65521u32)); }
     have to_integer(a_vec.0[3]) == to_integer(at(reduction_a, a_vec.0[3]) % 65521u32) by close() using { a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521) by { rewrite(to_integer(at(reduction_a, a_vec.0[3])), to_integer(at(vector_prefix, a_vec.0[3]))); close(); }
     have to_integer(a_vec.0[3]) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521) by close() using { to_integer(a_vec.0[3]) == to_integer(at(reduction_a, a_vec.0[3]) % 65521u32); to_integer(at(reduction_a, a_vec.0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_a, a_vec.0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521); };
     have truncating_remainder(adler_lane_a(to_integer(a), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == at(vector_prefix, adler_spec_a(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)))) by { rewrite(to_integer(a), to_integer(at(vector_prefix, a))); rewrite(to_integer(a_vec.0[0]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[0])), 65521)); rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521)); rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521)); rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521)); apply(integer::equal_substitute(truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[0])), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3]))), 65521), truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[0])), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3]))), 65521), truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[0])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521)), 65521), at(vector_prefix, adler_spec_a(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)))))); }
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % statement(13).call(0).result;
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32 by { rewrite(b_vec.0[0], at(reduction_b, b_vec.0[0]) % statement(13).call(0).result); close() using { statement(13).call(0).result == 65521u32; }; }
     have to_integer((at(reduction_b, b_vec.0[0])) % 65521u32) == truncating_remainder(to_integer((at(reduction_b, b_vec.0[0]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_b, b_vec.0[0])), 65521u32)); }
     have to_integer(b_vec.0[0]) == to_integer(at(reduction_b, b_vec.0[0]) % 65521u32) by close() using { b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[0])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[0]))); close(); }
     have to_integer(b_vec.0[0]) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[0])), 65521) by close() using { to_integer(b_vec.0[0]) == to_integer(at(reduction_b, b_vec.0[0]) % 65521u32); to_integer(at(reduction_b, b_vec.0[0]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[0])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[0])), 65521); };
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % statement(13).call(0).result;
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32 by { rewrite(b_vec.0[1], at(reduction_b, b_vec.0[1]) % statement(13).call(0).result); close() using { statement(13).call(0).result == 65521u32; }; }
     have to_integer((at(reduction_b, b_vec.0[1])) % 65521u32) == truncating_remainder(to_integer((at(reduction_b, b_vec.0[1]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_b, b_vec.0[1])), 65521u32)); }
     have to_integer(b_vec.0[1]) == to_integer(at(reduction_b, b_vec.0[1]) % 65521u32) by close() using { b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[1])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[1]))); close(); }
     have to_integer(b_vec.0[1]) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[1])), 65521) by close() using { to_integer(b_vec.0[1]) == to_integer(at(reduction_b, b_vec.0[1]) % 65521u32); to_integer(at(reduction_b, b_vec.0[1]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[1])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[1])), 65521); };
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % statement(13).call(0).result;
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32 by { rewrite(b_vec.0[2], at(reduction_b, b_vec.0[2]) % statement(13).call(0).result); close() using { statement(13).call(0).result == 65521u32; }; }
     have to_integer((at(reduction_b, b_vec.0[2])) % 65521u32) == truncating_remainder(to_integer((at(reduction_b, b_vec.0[2]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_b, b_vec.0[2])), 65521u32)); }
     have to_integer(b_vec.0[2]) == to_integer(at(reduction_b, b_vec.0[2]) % 65521u32) by close() using { b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[2])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[2]))); close(); }
     have to_integer(b_vec.0[2]) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[2])), 65521) by close() using { to_integer(b_vec.0[2]) == to_integer(at(reduction_b, b_vec.0[2]) % 65521u32); to_integer(at(reduction_b, b_vec.0[2]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[2])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[2])), 65521); };
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % statement(13).call(0).result;
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32 by { rewrite(b_vec.0[3], at(reduction_b, b_vec.0[3]) % statement(13).call(0).result); close() using { statement(13).call(0).result == 65521u32; }; }
     have to_integer((at(reduction_b, b_vec.0[3])) % 65521u32) == truncating_remainder(to_integer((at(reduction_b, b_vec.0[3]))), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer((at(reduction_b, b_vec.0[3])), 65521u32)); }
     have to_integer(b_vec.0[3]) == to_integer(at(reduction_b, b_vec.0[3]) % 65521u32) by close() using { b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32; };
     have truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[3])), 65521) by { rewrite(to_integer(at(reduction_b, b_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[3]))); close(); }
     have to_integer(b_vec.0[3]) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[3])), 65521) by close() using { to_integer(b_vec.0[3]) == to_integer(at(reduction_b, b_vec.0[3]) % 65521u32); to_integer(at(reduction_b, b_vec.0[3]) % 65521u32) == truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), to_integer(65521u32)); truncating_remainder(to_integer(at(reduction_b, b_vec.0[3])), 65521) == truncating_remainder(to_integer(at(vector_prefix, b_vec.0[3])), 65521); };
     step_until(statement(15).entry);
     have statement(14).call(0).result == 65521u32;
     have b == at(before_scalar_mod, b) % statement(14).call(0).result;
     have b == at(before_scalar_mod, b) % 65521u32 by { rewrite(b, at(before_scalar_mod, b) % statement(14).call(0).result); close() using { statement(14).call(0).result == 65521u32; }; }
     have to_integer(at(before_scalar_mod, b) % 65521u32) == truncating_remainder(to_integer(at(before_scalar_mod, b)), to_integer(65521u32)) by { apply(integer::uint32_remainder_to_integer(at(before_scalar_mod, b), 65521u32)); }
     have to_integer(b) == to_integer(at(before_scalar_mod, b) % 65521u32) by close() using { b == at(before_scalar_mod, b) % 65521u32; };
     have truncating_remainder(to_integer(at(before_scalar_mod, b)), 65521) == truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), 65521) by { rewrite(to_integer(at(before_scalar_mod, b)), to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a))); close(); }
     have to_integer(b) == truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), 65521) by {
      rewrite(to_integer(b), to_integer(at(before_scalar_mod, b) % 65521u32));
      rewrite(to_integer(at(before_scalar_mod, b) % 65521u32), truncating_remainder(to_integer(at(before_scalar_mod, b)), to_integer(65521u32)));
      close() using { truncating_remainder(to_integer(at(before_scalar_mod, b)), 65521) == truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), 65521); };
     }
     have truncating_remainder(adler_lane_b(to_integer(b), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]), to_integer(b_vec.0[0]), to_integer(b_vec.0[1]), to_integer(b_vec.0[2]), to_integer(b_vec.0[3])), 65521) == at(vector_prefix, adler_spec_b(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b)))) by { rewrite(to_integer(b), truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), 65521)); rewrite(to_integer(a_vec.0[1]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521)); rewrite(to_integer(a_vec.0[2]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521)); rewrite(to_integer(a_vec.0[3]), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521)); rewrite(to_integer(b_vec.0[0]), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[0])), 65521)); rewrite(to_integer(b_vec.0[1]), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[1])), 65521)); rewrite(to_integer(b_vec.0[2]), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[2])), 65521)); rewrite(to_integer(b_vec.0[3]), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[3])), 65521)); apply(integer::equal_substitute(truncating_remainder(adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[3]))), 65521), truncating_remainder(adler_lane_b(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, a_vec.0[1])), to_integer(at(vector_prefix, a_vec.0[2])), to_integer(at(vector_prefix, a_vec.0[3])), to_integer(at(vector_prefix, b_vec.0[0])), to_integer(at(vector_prefix, b_vec.0[1])), to_integer(at(vector_prefix, b_vec.0[2])), to_integer(at(vector_prefix, b_vec.0[3]))), 65521), truncating_remainder(adler_lane_b(truncating_remainder(to_integer(at(vector_prefix, b)) + to_integer((((bytes.len() - bytes.len() % 4u64) as u32) as i32)) * to_integer(at(vector_prefix, a)), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[1])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[2])), 65521), truncating_remainder(to_integer(at(vector_prefix, a_vec.0[3])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[0])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[1])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[2])), 65521), truncating_remainder(to_integer(at(vector_prefix, b_vec.0[3])), 65521)), 65521), at(vector_prefix, adler_spec_b(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b)))))); }
     mark weighted_b;
     have truncating_remainder(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))), 65521) == at(vector_prefix, adler_spec_b(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b))));
     step_until(statement(16).entry);
     have statement(12).call(0).result == 65521u32;
     have 65521u32 == statement(12).call(0).result by close() using { statement(12).call(0).result == 65521u32; };
     have a_vec.0[0] < statement(12).call(0).result;
     have a_vec.0[0] < 65521u32 by { rewrite(65521u32, statement(12).call(0).result); close(); }
     have a_vec.0[1] < statement(12).call(0).result;
     have a_vec.0[1] < 65521u32 by { rewrite(65521u32, statement(12).call(0).result); close(); }
     have a_vec.0[2] < statement(12).call(0).result;
     have a_vec.0[2] < 65521u32 by { rewrite(65521u32, statement(12).call(0).result); close(); }
     have a_vec.0[3] < statement(12).call(0).result;
     have a_vec.0[3] < 65521u32 by { rewrite(65521u32, statement(12).call(0).result); close(); }
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have to_integer(at(weighted_b, b_vec.0[0])) <= 65520;
     have to_integer(b_vec.0[0]) <= 262080 by close() using { to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4; to_integer(at(weighted_b, b_vec.0[0])) <= 65520; };
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(at(weighted_b, b_vec.0[1])) <= 65520;
     have to_integer(b_vec.0[1]) <= 262080 by close() using { to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4; to_integer(at(weighted_b, b_vec.0[1])) <= 65520; };
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(at(weighted_b, b_vec.0[2])) <= 65520;
     have to_integer(b_vec.0[2]) <= 262080 by close() using { to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4; to_integer(at(weighted_b, b_vec.0[2])) <= 65520; };
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(at(weighted_b, b_vec.0[3])) <= 65520;
     have to_integer(b_vec.0[3]) <= 262080 by close() using { to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4; to_integer(at(weighted_b, b_vec.0[3])) <= 65520; };
     mark correction_b;
     have to_integer(at(correction_b, b_vec.0[1])) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(at(correction_b, a_vec.0[1])) == to_integer(at(weighted_b, a_vec.0[1]));
     have to_integer(at(correction_b, b_vec.0[2])) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(at(correction_b, a_vec.0[2])) == to_integer(at(weighted_b, a_vec.0[2]));
     have to_integer(at(correction_b, b_vec.0[3])) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(at(correction_b, a_vec.0[3])) == to_integer(at(weighted_b, a_vec.0[3]));
     apply(adler_recombine_lane_1(a_vec.0[1], b_vec.0[1]));
     apply(adler_recombine_lane_2(a_vec.0[2], b_vec.0[2]));
     apply(adler_recombine_lane_3(a_vec.0[3], b_vec.0[3]));
     apply(adler_recombine_difference(a_vec.0[1]));
     apply(adler_recombine_difference(a_vec.0[2]));
     have 65521u32 - a_vec.0[2] <= 4294967295u32 / 2u32 by {
      have to_integer(65521u32) <= to_integer(4294967295u32 / 2u32) by close();
      apply(integer::le_transitive(to_integer(65521u32 - a_vec.0[2]), to_integer(65521u32), to_integer(4294967295u32 / 2u32)));
      apply(integer::uint32_to_integer_less_equal_implies_less_equal(65521u32 - a_vec.0[2], 4294967295u32 / 2u32));
     }
     apply(adler_recombine_difference(a_vec.0[3]));
     have 65521u32 - a_vec.0[3] <= 4294967295u32 / 3u32 by {
      have to_integer(65521u32) <= to_integer(4294967295u32 / 3u32) by close();
      apply(integer::le_transitive(to_integer(65521u32 - a_vec.0[3]), to_integer(65521u32), to_integer(4294967295u32 / 3u32)));
      apply(integer::uint32_to_integer_less_equal_implies_less_equal(65521u32 - a_vec.0[3], 4294967295u32 / 3u32));
     }
     have to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) == to_integer(at(correction_b, b_vec.0[1])) + (65521 - to_integer(at(correction_b, a_vec.0[1]))) * 1;
     have to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) == to_integer(at(correction_b, b_vec.0[2])) + (65521 - to_integer(at(correction_b, a_vec.0[2]))) * 2;
     have to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) == to_integer(at(correction_b, b_vec.0[3])) + (65521 - to_integer(at(correction_b, a_vec.0[3]))) * 3;
     have separate(memory(b_vec.0[1..2]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     have separate(memory(((((b_vec as (uint8 *)) + 4) as (uint32 *)))[0..1]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     step_until(statement(17).entry);
     have statement(16).call(0).result == 65521u32;
     have separate(memory(b_vec.0[2..3]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     have separate(memory(((((b_vec as (uint8 *)) + 8) as (uint32 *)))[0..1]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     step_until(statement(18).entry);
     have statement(17).call(0).result == 65521u32;
     have separate(memory(b_vec.0[3..4]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     have separate(memory(((((b_vec as (uint8 *)) + 12) as (uint32 *)))[0..1]), at(function.entry, memory(bytes[0u64..program::bytes.len()]))) by close();
     step_until(statement(19).entry);
     have statement(18).call(0).result == 65521u32;
     step_until(loop(3).entry);
     have b_vec.0[1] == at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1])) by close();
     have to_integer(b_vec.0[1]) == to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))) by {
      apply(adler_equal_stored_words(b_vec.0[1], at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))));
     }
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[1]))) * 1 by {
      rewrite(to_integer(b_vec.0[1]), to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))));
      rewrite(to_integer(at(correction_b, b_vec.0[1]) + (65521u32 - at(correction_b, a_vec.0[1]))), to_integer(at(correction_b, b_vec.0[1])) + (65521 - to_integer(at(correction_b, a_vec.0[1]))) * 1);
      rewrite(to_integer(at(correction_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[1])) * 4);
      rewrite(to_integer(at(correction_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[1])));
      close();
     }
     have b_vec.0[2] == at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32) by close();
     have to_integer(b_vec.0[2]) == to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)) by {
      apply(adler_equal_stored_words(b_vec.0[2], at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)));
     }
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[2]))) * 2 by {
      rewrite(to_integer(b_vec.0[2]), to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)));
      rewrite(to_integer(at(correction_b, b_vec.0[2]) + ((65521u32 - at(correction_b, a_vec.0[2])) * 2u32)), to_integer(at(correction_b, b_vec.0[2])) + (65521 - to_integer(at(correction_b, a_vec.0[2]))) * 2);
      rewrite(to_integer(at(correction_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[2])) * 4);
      rewrite(to_integer(at(correction_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[2])));
      close();
     }
     have b_vec.0[3] == at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32) by close();
     have to_integer(b_vec.0[3]) == to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)) by {
      apply(adler_equal_stored_words(b_vec.0[3], at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)));
     }
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4 + (65521 - to_integer(at(weighted_b, a_vec.0[3]))) * 3 by {
      rewrite(to_integer(b_vec.0[3]), to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)));
      rewrite(to_integer(at(correction_b, b_vec.0[3]) + ((65521u32 - at(correction_b, a_vec.0[3])) * 3u32)), to_integer(at(correction_b, b_vec.0[3])) + (65521 - to_integer(at(correction_b, a_vec.0[3]))) * 3);
      rewrite(to_integer(at(correction_b, b_vec.0[3])), to_integer(at(weighted_b, b_vec.0[3])) * 4);
      rewrite(to_integer(at(correction_b, a_vec.0[3])), to_integer(at(weighted_b, a_vec.0[3])));
      close();
     }
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have a <= 65520u32 by close();
     have to_integer(a) <= to_integer(65520u32);
     step_until(loop(3).statement(0).entry);
     have av == a_vec.0[0] by close();
     have to_integer(a_vec.0[0]) <= 65520 by close();
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[0]); close(); }
     have to_integer(a) + to_integer(av) <= 4294967295 by close() using { to_integer(a) <= 65520; to_integer(av) <= 65520; };
     mark small_sum_a_0;
     have to_integer(at(small_sum_a_0, a)) == to_integer(at(vector_prefix, a)) by close();
     have to_integer(at(small_sum_a_0, av)) == to_integer(a_vec.0[0]) by close();
     apply(integer::uint32_add_to_integer(at(small_sum_a_0, a), at(small_sum_a_0, av)));
     step_until(assignment(a, 1).entry); step();
     have a == at(small_sum_a_0, a) + at(small_sum_a_0, av) by close();
     have to_integer(a) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, av)) by close();
     have to_integer(a) <= 131040 by close() using {
      to_integer(a) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, av));
      to_integer(at(small_sum_a_0, a)) <= 65520;
      to_integer(at(small_sum_a_0, av)) <= 65520;
     };
     have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) by close() using {
      to_integer(a) == to_integer(at(small_sum_a_0, a)) + to_integer(at(small_sum_a_0, av));
      to_integer(at(small_sum_a_0, a)) == to_integer(at(vector_prefix, a));
      to_integer(at(small_sum_a_0, av)) == to_integer(a_vec.0[0]);
     };

     step(); step();
     step_until(loop(3).statement(0).entry);
     have av == a_vec.0[1] by close();
     have to_integer(a_vec.0[1]) <= 65520 by close();
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[1]); close(); }
     have to_integer(a) + to_integer(av) <= 4294967295 by close() using { to_integer(a) <= 131040; to_integer(av) <= 65520; };
     mark small_sum_a_1;
     have to_integer(at(small_sum_a_1, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) by close();
     have to_integer(at(small_sum_a_1, av)) == to_integer(a_vec.0[1]) by close();
     apply(integer::uint32_add_to_integer(at(small_sum_a_1, a), at(small_sum_a_1, av)));
     step_until(assignment(a, 1).entry); step();
     have a == at(small_sum_a_1, a) + at(small_sum_a_1, av) by close();
     have to_integer(a) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, av)) by close();
     have to_integer(a) <= 196560 by close() using {
      to_integer(a) == to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, av));
      to_integer(at(small_sum_a_1, a)) <= 131040;
      to_integer(at(small_sum_a_1, av)) <= 65520;
     };
     have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) by {
      rewrite(to_integer(a), to_integer(at(small_sum_a_1, a)) + to_integer(at(small_sum_a_1, av)));
      rewrite(to_integer(at(small_sum_a_1, a)), to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]));
      rewrite(to_integer(at(small_sum_a_1, av)), to_integer(a_vec.0[1]));
      close();
     }

     step(); step();
     step_until(loop(3).statement(0).entry);
     have av == a_vec.0[2] by close();
     have to_integer(a_vec.0[2]) <= 65520 by close();
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[2]); close(); }
     have to_integer(a) + to_integer(av) <= 4294967295 by close() using { to_integer(a) <= 196560; to_integer(av) <= 65520; };
     mark small_sum_a_2;
     have to_integer(at(small_sum_a_2, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) by close();
     have to_integer(at(small_sum_a_2, av)) == to_integer(a_vec.0[2]) by close();
     apply(integer::uint32_add_to_integer(at(small_sum_a_2, a), at(small_sum_a_2, av)));
     step_until(assignment(a, 1).entry); step();
     have a == at(small_sum_a_2, a) + at(small_sum_a_2, av) by close();
     have to_integer(a) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, av)) by close();
     have to_integer(a) <= 262080 by close() using {
      to_integer(a) == to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, av));
      to_integer(at(small_sum_a_2, a)) <= 196560;
      to_integer(at(small_sum_a_2, av)) <= 65520;
     };
     have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) by {
      rewrite(to_integer(a), to_integer(at(small_sum_a_2, a)) + to_integer(at(small_sum_a_2, av)));
      rewrite(to_integer(at(small_sum_a_2, a)), to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]));
      rewrite(to_integer(at(small_sum_a_2, av)), to_integer(a_vec.0[2]));
      close();
     }

     step(); step();
     step_until(loop(3).statement(0).entry);
     have av == a_vec.0[3] by close();
     have to_integer(a_vec.0[3]) <= 65520 by close();
     have to_integer(av) <= 65520 by { rewrite(av, a_vec.0[3]); close(); }
     have to_integer(a) + to_integer(av) <= 4294967295 by close() using { to_integer(a) <= 262080; to_integer(av) <= 65520; };
     mark small_sum_a_3;
     have to_integer(at(small_sum_a_3, a)) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) by close();
     have to_integer(at(small_sum_a_3, av)) == to_integer(a_vec.0[3]) by close();
     apply(integer::uint32_add_to_integer(at(small_sum_a_3, a), at(small_sum_a_3, av)));
     step_until(assignment(a, 1).entry); step();
     have a == at(small_sum_a_3, a) + at(small_sum_a_3, av) by close();
     have to_integer(a) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, av)) by close();
     have to_integer(a) <= 327600 by close() using {
      to_integer(a) == to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, av));
      to_integer(at(small_sum_a_3, a)) <= 262080;
      to_integer(at(small_sum_a_3, av)) <= 65520;
     };
     have to_integer(a) == to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]) + to_integer(a_vec.0[3]) by {
      rewrite(to_integer(a), to_integer(at(small_sum_a_3, a)) + to_integer(at(small_sum_a_3, av)));
      rewrite(to_integer(at(small_sum_a_3, a)), to_integer(at(vector_prefix, a)) + to_integer(a_vec.0[0]) + to_integer(a_vec.0[1]) + to_integer(a_vec.0[2]));
      rewrite(to_integer(at(small_sum_a_3, av)), to_integer(a_vec.0[3]));
      close() using {};
     }

     have to_integer(a) == adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])) by { unfold(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); close(); }
     have truncating_remainder(to_integer(a), 65521) == at(vector_prefix, adler_spec_a(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)))) by { rewrite(to_integer(a), adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3]))); close() using { truncating_remainder(adler_lane_a(to_integer(at(vector_prefix, a)), to_integer(a_vec.0[0]), to_integer(a_vec.0[1]), to_integer(a_vec.0[2]), to_integer(a_vec.0[3])), 65521) == at(vector_prefix, adler_spec_a(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)))); }; }
     step_until(loop(4).entry);
     have statement(14).call(0).result == 65521u32;
     have 65521u32 == statement(14).call(0).result by close() using { statement(14).call(0).result == 65521u32; };
     have b == at(before_scalar_mod, b) % statement(14).call(0).result;
     have statement(14).call(0).result != 0u32 by { rewrite(statement(14).call(0).result, 65521u32); close(); }
     have at(before_scalar_mod, b) % statement(14).call(0).result < statement(14).call(0).result by { apply(integer::uint32_remainder_less_than_divisor(at(before_scalar_mod, b), statement(14).call(0).result)); }
     have b < statement(14).call(0).result by { rewrite(b, at(before_scalar_mod, b) % statement(14).call(0).result); close(); }
     have b < 65521u32 by { rewrite(65521u32, statement(14).call(0).result); close(); }
     have to_integer(b) < to_integer(65521u32);
     have to_integer(b) <= 65520 by close() using { to_integer(b) < 65521; };
     have to_integer(b_vec.0[0]) <= 262080;
     step_until(loop(4).statement(0).entry);
     have bv == b_vec.0[0] by close();
     have to_integer(b_vec.0[0]) <= 262080 by close();
     have to_integer(bv) <= 262080 by { rewrite(bv, b_vec.0[0]); close(); }
     have to_integer(b) + to_integer(bv) <= 4294967295 by close() using { to_integer(b) <= 65520; to_integer(bv) <= 262080; };
     mark small_sum_b_0;
     have to_integer(at(small_sum_b_0, b)) == to_integer(at(weighted_b, b)) by close();
     have to_integer(at(small_sum_b_0, bv)) == to_integer(b_vec.0[0]) by close();
     apply(integer::uint32_add_to_integer(at(small_sum_b_0, b), at(small_sum_b_0, bv)));
     step_until(assignment(b, 5).entry); step();
     have b == at(small_sum_b_0, b) + at(small_sum_b_0, bv) by close();
     have to_integer(b) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, bv)) by close();
     have to_integer(b) <= 327600 by close() using {
      to_integer(b) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, bv));
      to_integer(at(small_sum_b_0, b)) <= 65520;
      to_integer(at(small_sum_b_0, bv)) <= 262080;
     };
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) by close() using {
      to_integer(b) == to_integer(at(small_sum_b_0, b)) + to_integer(at(small_sum_b_0, bv));
      to_integer(at(small_sum_b_0, b)) == to_integer(at(weighted_b, b));
      to_integer(at(small_sum_b_0, bv)) == to_integer(b_vec.0[0]);
     };

     step(); step();
     step_until(loop(4).statement(0).entry);
     have bv == b_vec.0[1] by close();
     have to_integer(b_vec.0[1]) <= 327601 by close();
     have to_integer(bv) <= 327601 by { rewrite(bv, b_vec.0[1]); close(); }
     have to_integer(b) + to_integer(bv) <= 4294967295 by close() using { to_integer(b) <= 327600; to_integer(bv) <= 327601; };
     mark small_sum_b_1;
     have to_integer(at(small_sum_b_1, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) by close();
     have to_integer(at(small_sum_b_1, bv)) == to_integer(b_vec.0[1]) by close();
     apply(integer::uint32_add_to_integer(at(small_sum_b_1, b), at(small_sum_b_1, bv)));
     step_until(assignment(b, 5).entry); step();
     have b == at(small_sum_b_1, b) + at(small_sum_b_1, bv) by close();
     have to_integer(b) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, bv)) by close();
     have to_integer(b) <= 655201 by close() using {
      to_integer(b) == to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, bv));
      to_integer(at(small_sum_b_1, b)) <= 327600;
      to_integer(at(small_sum_b_1, bv)) <= 327601;
     };
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) by {
      rewrite(to_integer(b), to_integer(at(small_sum_b_1, b)) + to_integer(at(small_sum_b_1, bv)));
      rewrite(to_integer(at(small_sum_b_1, b)), to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]));
      rewrite(to_integer(at(small_sum_b_1, bv)), to_integer(b_vec.0[1]));
      close();
     }

     step(); step();
     step_until(loop(4).statement(0).entry);
     have bv == b_vec.0[2] by close();
     have to_integer(b_vec.0[2]) <= 393122 by close();
     have to_integer(bv) <= 393122 by { rewrite(bv, b_vec.0[2]); close(); }
     have to_integer(b) + to_integer(bv) <= 4294967295 by close() using { to_integer(b) <= 655201; to_integer(bv) <= 393122; };
     mark small_sum_b_2;
     have to_integer(at(small_sum_b_2, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) by close();
     have to_integer(at(small_sum_b_2, bv)) == to_integer(b_vec.0[2]) by close();
     apply(integer::uint32_add_to_integer(at(small_sum_b_2, b), at(small_sum_b_2, bv)));
     step_until(assignment(b, 5).entry); step();
     have b == at(small_sum_b_2, b) + at(small_sum_b_2, bv) by close();
     have to_integer(b) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, bv)) by close();
     have to_integer(b) <= 1048323 by close() using {
      to_integer(b) == to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, bv));
      to_integer(at(small_sum_b_2, b)) <= 655201;
      to_integer(at(small_sum_b_2, bv)) <= 393122;
     };
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) by {
      rewrite(to_integer(b), to_integer(at(small_sum_b_2, b)) + to_integer(at(small_sum_b_2, bv)));
      rewrite(to_integer(at(small_sum_b_2, b)), to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]));
      rewrite(to_integer(at(small_sum_b_2, bv)), to_integer(b_vec.0[2]));
      close();
     }

     step(); step();
     step_until(loop(4).statement(0).entry);
     have bv == b_vec.0[3] by close();
     have to_integer(b_vec.0[3]) <= 458643 by close();
     have to_integer(bv) <= 458643 by { rewrite(bv, b_vec.0[3]); close(); }
     have to_integer(b) + to_integer(bv) <= 4294967295 by close() using { to_integer(b) <= 1048323; to_integer(bv) <= 458643; };
     mark small_sum_b_3;
     have to_integer(at(small_sum_b_3, b)) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) by close();
     have to_integer(at(small_sum_b_3, bv)) == to_integer(b_vec.0[3]) by close();
     apply(integer::uint32_add_to_integer(at(small_sum_b_3, b), at(small_sum_b_3, bv)));
     step_until(assignment(b, 5).entry); step();
     have b == at(small_sum_b_3, b) + at(small_sum_b_3, bv) by close();
     have to_integer(b) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, bv)) by close();
     have to_integer(b) <= 1506966 by close() using {
      to_integer(b) == to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, bv));
      to_integer(at(small_sum_b_3, b)) <= 1048323;
      to_integer(at(small_sum_b_3, bv)) <= 458643;
     };
     have to_integer(b) == to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]) + to_integer(b_vec.0[3]) by {
      rewrite(to_integer(b), to_integer(at(small_sum_b_3, b)) + to_integer(at(small_sum_b_3, bv)));
      rewrite(to_integer(at(small_sum_b_3, b)), to_integer(at(weighted_b, b)) + to_integer(b_vec.0[0]) + to_integer(b_vec.0[1]) + to_integer(b_vec.0[2]));
      rewrite(to_integer(at(small_sum_b_3, bv)), to_integer(b_vec.0[3]));
      close();
     }

     step(); step();
     have backing_length == old(bytes.len()) by close();
     have remainder.len() == backing_length % 4u64 by close();
     apply(adler_small_tail_metadata(backing_length));
     have remainder.len() <= 3u64 by { rewrite(remainder.len(), backing_length % 4u64); close(); }
     have remainder.len() <= 2147483647u64 by close() using { remainder.len() <= 3u64; };
     have to_integer(b) == adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))) by {
       apply(adler_recombined_lane_b(
           to_integer(b),
           to_integer(at(weighted_b, b)),
           to_integer(at(weighted_b, a_vec.0[1])),
           to_integer(at(weighted_b, a_vec.0[2])),
           to_integer(at(weighted_b, a_vec.0[3])),
           to_integer(at(weighted_b, b_vec.0[0])),
           to_integer(at(weighted_b, b_vec.0[1])),
           to_integer(at(weighted_b, b_vec.0[2])),
           to_integer(at(weighted_b, b_vec.0[3])),
           to_integer(b_vec.0[0]),
           to_integer(b_vec.0[1]),
           to_integer(b_vec.0[2]),
           to_integer(b_vec.0[3])
       ));
     }
     have truncating_remainder(to_integer(b), 65521) == at(vector_prefix, adler_spec_b(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b)))) by { rewrite(to_integer(b), adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3])))); close() using { truncating_remainder(adler_lane_b(to_integer(at(weighted_b, b)), to_integer(at(weighted_b, a_vec.0[1])), to_integer(at(weighted_b, a_vec.0[2])), to_integer(at(weighted_b, a_vec.0[3])), to_integer(at(weighted_b, b_vec.0[0])), to_integer(at(weighted_b, b_vec.0[1])), to_integer(at(weighted_b, b_vec.0[2])), to_integer(at(weighted_b, b_vec.0[3]))), 65521) == at(vector_prefix, adler_spec_b(bytes.as_ptr(), (((bytes.len() - bytes.len() % 4u64) as u32) as i32), to_integer(at(vector_prefix, a)), to_integer(at(vector_prefix, b)))); }; }
     step_until(loop(5).entry);
     have to_integer(backing_length - backing_length % 4u64) <= to_integer(backing_length) by close() using { backing_length - backing_length % 4u64 <= backing_length; to_integer(backing_length - backing_length % 4u64) == to_integer(backing_length) - to_integer(backing_length % 4u64); };
     apply(adler_small_prefix_within_full(backing_length));
     apply(adler_small_signed_tail(backing_length));
     apply(adler_small_tail_indices(backing_length));
     have ((remainder.len() as u32) as i32) == (((backing_length % 4u64) as u32) as i32) by { rewrite(remainder.len(), backing_length % 4u64); close() using {}; }
     have 0 <= ((remainder.len() as u32) as i32) by { rewrite(((remainder.len() as u32) as i32), (((backing_length % 4u64) as u32) as i32)); close(); }
     have ((remainder.len() as u32) as i32) <= 3 by { rewrite(((remainder.len() as u32) as i32), (((backing_length % 4u64) as u32) as i32)); close(); }
     have ((remainder.len() as u32) as i32) <= ((backing_length as u32) as i32) by { rewrite(((remainder.len() as u32) as i32), (((backing_length % 4u64) as u32) as i32)); close(); }
     have ((backing_length as u32) as i32) - ((remainder.len() as u32) as i32) == (((backing_length - backing_length % 4u64) as u32) as i32) by { rewrite(((remainder.len() as u32) as i32), (((backing_length % 4u64) as u32) as i32)); have 0 <= (((backing_length % 4u64) as u32) as i32) by close(); have 0 <= ((backing_length as u32) as i32) by close(); have ((backing_length as u32) as i32) <= 22207 by close(); have to_integer(((backing_length as u32) as i32) - (((backing_length % 4u64) as u32) as i32)) == to_integer(((backing_length as u32) as i32)) - to_integer((((backing_length % 4u64) as u32) as i32)) by close() using { 0 <= (((backing_length % 4u64) as u32) as i32); (((backing_length % 4u64) as u32) as i32) <= ((backing_length as u32) as i32); 0 <= ((backing_length as u32) as i32); ((backing_length as u32) as i32) <= 22207; }; close() using { to_integer(((backing_length as u32) as i32) - (((backing_length % 4u64) as u32) as i32)) == to_integer(((backing_length as u32) as i32)) - to_integer((((backing_length % 4u64) as u32) as i32)); to_integer(((backing_length as u32) as i32) - (((backing_length % 4u64) as u32) as i32)) == to_integer((((backing_length - backing_length % 4u64) as u32) as i32)); }; }
      have loop(5).iter.len() == remainder.len();
      have ((loop(5).iter.len() as u32) as i32) == ((remainder.len() as u32) as i32) by { rewrite(loop(5).iter.len(), remainder.len()); close(); }
      have remainder.len() <= 3u64 by { rewrite(remainder.len(), backing_length % 4u64); close(); }
      have remainder.len() <= backing_length by { rewrite(remainder.len(), backing_length % 4u64); close(); }
      have loop(5).iter.len() <= remainder.len() by { rewrite(loop(5).iter.len(), remainder.len()); close(); }
     have 0 <= ((loop(5).iter.len() as u32) as i32) and ((loop(5).iter.len() as u32) as i32) <= ((remainder.len() as u32) as i32) by { rewrite(((loop(5).iter.len() as u32) as i32), ((remainder.len() as u32) as i32)); all { 0 <= ((remainder.len() as u32) as i32) => { close(); } ((remainder.len() as u32) as i32) <= ((remainder.len() as u32) as i32) => { close() using {}; } } }
      have (loop(5).iter.as_slice().as_ptr() as Pointer) == (remainder as Pointer) by close();
      have loop(5).iter.as_slice().as_ptr() == remainder by close() using {
       (loop(5).iter.as_slice().as_ptr() as Pointer) == (remainder as Pointer);
      };
      have remainder == bytes.as_ptr() + (backing_length - backing_length % 4u64) by close();
      have backing_length - loop(5).iter.len() == backing_length - backing_length % 4u64 by { rewrite(loop(5).iter.len(), remainder.len()); rewrite(remainder.len(), backing_length % 4u64); close(); }
      have loop(5).iter.as_slice().as_ptr() == bytes.as_ptr() + (backing_length - backing_length % 4u64) by { rewrite(loop(5).iter.as_slice().as_ptr(), remainder); close(); }
     have adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)) == 0 by { unfold(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32))); rewrite(((loop(5).iter.len() as u32) as i32), ((remainder.len() as u32) as i32)); close() using {}; }
     have adler_tail_a_ceiling(0) == 327600 by { unfold(adler_tail_a_ceiling(0)); close() using {}; }
     have adler_tail_b_ceiling(0) == 1506966 by { unfold(adler_tail_b_ceiling(0)); close() using {}; }
     have 0 <= to_integer(a);
     have to_integer(a) <= 4294967295;
     have 0 <= to_integer(b);
     have to_integer(b) <= 4294967295;
     have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)), 0); rewrite(adler_tail_a_ceiling(0), 327600); close(); }
     have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)), 0); rewrite(adler_tail_b_ceiling(0), 1506966); close(); }
     have old(to_integer((self.a as u32))) == to_integer(at(vector_prefix, a));
     have old(to_integer((self.b as u32))) == to_integer(at(vector_prefix, b));
     have 0 <= to_integer((old((self.a as u32))));
     have to_integer((old((self.a as u32)))) <= 4294967295;
     have to_integer((old((self.a as u32)))) <= to_integer(65520u32);
     have ((loop(5).iter.len() as u32) as i32) <= ((backing_length as u32) as i32) by close() using { ((loop(5).iter.len() as u32) as i32) == ((remainder.len() as u32) as i32); ((remainder.len() as u32) as i32) <= ((backing_length as u32) as i32); };
     have defined((((backing_length as u32) as i32)) - (((loop(5).iter.len() as u32) as i32)));
     have (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) == (((backing_length - backing_length % 4u64) as u32) as i32) by { rewrite(((loop(5).iter.len() as u32) as i32), ((remainder.len() as u32) as i32)); close(); }
     have 0 <= old(to_integer((self.a as u32))) by close();
     have old(to_integer((self.a as u32))) <= 65520 by close();
     have 0 <= to_integer((at(vector_prefix, b)));
     have to_integer((at(vector_prefix, b))) <= 4294967295;
     have exists (n: int32) { n == (((backing_length - backing_length % 4u64) as u32) as i32) } by { witness((((backing_length - backing_length % 4u64) as u32) as i32)); close(); }
     let tail_prefix_count = obtain(exists (n: int32) { n == (((backing_length - backing_length % 4u64) as u32) as i32) });
     have (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) == tail_prefix_count by close();
     have tail_prefix_count == at(vector_prefix, (((bytes.len() - bytes.len() % 4u64) as u32) as i32)) by close();
     have 0 <= tail_prefix_count by close();
     have forall (k: int32) { 0 <= k and k < tail_prefix_count implies bytes[k] == at(vector_prefix, bytes[k]) } by {
      intro() {
       intro() {
        have at(region(366).entry, bytes[k]) == at(vector_prefix, bytes[k]) by close();
        have separate(region(366).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(366).exit, bytes[k]) == at(region(366).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(366)); }
        have at(region(366).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(366).exit, bytes[k]) == at(region(366).entry, bytes[k]);
         at(region(366).entry, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have at(region(376).entry, bytes[k]) == at(region(366).exit, bytes[k]) by close();
        have separate(region(376).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(376).exit, bytes[k]) == at(region(376).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(376)); }
        have at(region(376).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(376).exit, bytes[k]) == at(region(376).entry, bytes[k]);
         at(region(376).entry, bytes[k]) == at(region(366).exit, bytes[k]);
         at(region(366).exit, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have at(region(391).entry, bytes[k]) == at(region(376).exit, bytes[k]) by close();
        have separate(region(391).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(391).exit, bytes[k]) == at(region(391).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(391)); }
        have at(region(391).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(391).exit, bytes[k]) == at(region(391).entry, bytes[k]);
         at(region(391).entry, bytes[k]) == at(region(376).exit, bytes[k]);
         at(region(376).exit, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have at(region(414).entry, bytes[k]) == at(region(391).exit, bytes[k]) by close();
        have separate(region(414).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(414).exit, bytes[k]) == at(region(414).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(414)); }
        have at(region(414).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(414).exit, bytes[k]) == at(region(414).entry, bytes[k]);
         at(region(414).entry, bytes[k]) == at(region(391).exit, bytes[k]);
         at(region(391).exit, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have at(region(439).entry, bytes[k]) == at(region(414).exit, bytes[k]) by close();
        have separate(region(439).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(439).exit, bytes[k]) == at(region(439).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(439)); }
        have at(region(439).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(439).exit, bytes[k]) == at(region(439).entry, bytes[k]);
         at(region(439).entry, bytes[k]) == at(region(414).exit, bytes[k]);
         at(region(414).exit, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have at(region(464).entry, bytes[k]) == at(region(439).exit, bytes[k]) by close();
        have separate(region(464).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(464).exit, bytes[k]) == at(region(464).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(464)); }
        have at(region(464).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(464).exit, bytes[k]) == at(region(464).entry, bytes[k]);
         at(region(464).entry, bytes[k]) == at(region(439).exit, bytes[k]);
         at(region(439).exit, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have bytes[k] == at(region(464).exit, bytes[k]) by close();
        close() using { bytes[k] == at(region(464).exit, bytes[k]); at(region(464).exit, bytes[k]) == at(vector_prefix, bytes[k]); };
       }
      }
     }
     have forall (k: int32) { 0 <= k and k < ((backing_length as u32) as i32) implies bytes[k] == at(vector_prefix, bytes[k]) } by {
      intro() {
       intro() {
        have at(region(366).entry, bytes[k]) == at(vector_prefix, bytes[k]) by close();
        have separate(region(366).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(366).exit, bytes[k]) == at(region(366).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(366)); }
        have at(region(366).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(366).exit, bytes[k]) == at(region(366).entry, bytes[k]);
         at(region(366).entry, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have at(region(376).entry, bytes[k]) == at(region(366).exit, bytes[k]) by close();
        have separate(region(376).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(376).exit, bytes[k]) == at(region(376).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(376)); }
        have at(region(376).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(376).exit, bytes[k]) == at(region(376).entry, bytes[k]);
         at(region(376).entry, bytes[k]) == at(region(366).exit, bytes[k]);
         at(region(366).exit, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have at(region(391).entry, bytes[k]) == at(region(376).exit, bytes[k]) by close();
        have separate(region(391).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(391).exit, bytes[k]) == at(region(391).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(391)); }
        have at(region(391).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(391).exit, bytes[k]) == at(region(391).entry, bytes[k]);
         at(region(391).entry, bytes[k]) == at(region(376).exit, bytes[k]);
         at(region(376).exit, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have at(region(414).entry, bytes[k]) == at(region(391).exit, bytes[k]) by close();
        have separate(region(414).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(414).exit, bytes[k]) == at(region(414).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(414)); }
        have at(region(414).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(414).exit, bytes[k]) == at(region(414).entry, bytes[k]);
         at(region(414).entry, bytes[k]) == at(region(391).exit, bytes[k]);
         at(region(391).exit, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have at(region(439).entry, bytes[k]) == at(region(414).exit, bytes[k]) by close();
        have separate(region(439).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(439).exit, bytes[k]) == at(region(439).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(439)); }
        have at(region(439).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(439).exit, bytes[k]) == at(region(439).entry, bytes[k]);
         at(region(439).entry, bytes[k]) == at(region(414).exit, bytes[k]);
         at(region(414).exit, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have at(region(464).entry, bytes[k]) == at(region(439).exit, bytes[k]) by close();
        have separate(region(464).footprint, at(vector_prefix, memory(bytes[k]))) by close();
        have at(region(464).exit, bytes[k]) == at(region(464).entry, bytes[k]) by { preserve(at(vector_prefix, memory(bytes[k])), region(464)); }
        have at(region(464).exit, bytes[k]) == at(vector_prefix, bytes[k]) by close() using {
         at(region(464).exit, bytes[k]) == at(region(464).entry, bytes[k]);
         at(region(464).entry, bytes[k]) == at(region(439).exit, bytes[k]);
         at(region(439).exit, bytes[k]) == at(vector_prefix, bytes[k]);
        };
        have bytes[k] == at(region(464).exit, bytes[k]) by close();
        close() using { bytes[k] == at(region(464).exit, bytes[k]); at(region(464).exit, bytes[k]) == at(vector_prefix, bytes[k]); };
       }
      }
     }
     have forall (k: int32) { 0 <= k and k < ((backing_length as u32) as i32) implies bytes[k] == old(bytes[k]) } by {
      intro() {
       intro() {
        have bytes[k] == at(vector_prefix, bytes[k]) by close();
        instantiate(forall (i: int32) { 0 <= i and i < ((backing_length as u32) as i32) implies at(vector_prefix, bytes[i]) == old(bytes[i]) }, k);
        have at(vector_prefix, bytes[k]) == old(bytes[k]) by close() using {
         0 <= k;
         k < ((backing_length as u32) as i32);
         0 <= k and k < ((backing_length as u32) as i32) implies at(vector_prefix, bytes[k]) == old(bytes[k]);
        };
        close() using { bytes[k] == at(vector_prefix, bytes[k]); at(vector_prefix, bytes[k]) == old(bytes[k]); };
       }
      }
     }
     apply(adler_spec_extensional(bytes.as_ptr(), at(vector_prefix, bytes.as_ptr()), tail_prefix_count, old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
     have adler_spec_a(bytes.as_ptr(), tail_prefix_count, old(to_integer((self.a as u32)))) == at(vector_prefix, adler_spec_a(bytes.as_ptr(), tail_prefix_count, to_integer(a))) by close();
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes.as_ptr(), (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), old(to_integer((self.a as u32)))) by {
      rewrite((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), tail_prefix_count);
      rewrite(adler_spec_a(bytes.as_ptr(), tail_prefix_count, old(to_integer((self.a as u32)))), at(vector_prefix, adler_spec_a(bytes.as_ptr(), tail_prefix_count, to_integer(a))));
      rewrite(tail_prefix_count, at(vector_prefix, (((bytes.len() - bytes.len() % 4u64) as u32) as i32)));
      close();
     }
     have adler_spec_b(bytes.as_ptr(), tail_prefix_count, old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == at(vector_prefix, adler_spec_b(bytes.as_ptr(), tail_prefix_count, to_integer(a), to_integer(b))) by close();
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes.as_ptr(), (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by {
      rewrite((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), tail_prefix_count);
      rewrite(adler_spec_b(bytes.as_ptr(), tail_prefix_count, old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))), at(vector_prefix, adler_spec_b(bytes.as_ptr(), tail_prefix_count, to_integer(a), to_integer(b))));
      rewrite(tail_prefix_count, at(vector_prefix, (((bytes.len() - bytes.len() % 4u64) as u32) as i32)));
      close();
     }
     loop {
      decreases loop(5).iter.len();
      views bytes[0u64..(bytes.len() + remainder.len())];
      invariant backing_length <= 22207u64;
      invariant bytes.len() == backing_length - backing_length % 4u64;
      invariant bytes.len() + remainder.len() == backing_length;
      invariant bytes.as_ptr() == old(bytes.as_ptr());
      invariant forall (k: int32) { 0 <= k and k < ((backing_length as u32) as i32) implies bytes[k] == old(bytes[k]) };
      invariant 0 <= ((remainder.len() as u32) as i32) and ((remainder.len() as u32) as i32) <= 3;
      invariant ((remainder.len() as u32) as i32) <= ((backing_length as u32) as i32);
      invariant 0 <= ((backing_length as u32) as i32) and ((backing_length as u32) as i32) <= 22207;
      invariant 0 <= ((loop(5).iter.len() as u32) as i32) and ((loop(5).iter.len() as u32) as i32) <= ((remainder.len() as u32) as i32);
       invariant remainder.len() <= 3u64;
       invariant remainder.len() <= backing_length;
       invariant loop(5).iter.len() <= remainder.len();
       invariant loop(5).iter.as_slice().as_ptr() == bytes.as_ptr() + (backing_length - loop(5).iter.len());
      invariant defined((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)));
      invariant 0 <= old(to_integer((self.a as u32))) and old(to_integer((self.a as u32))) <= 65520;
      invariant 0 <= old(to_integer((self.b as u32)));
      invariant truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes.as_ptr(), (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), old(to_integer((self.a as u32))));
      invariant truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes.as_ptr(), (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))));
      invariant 0 <= to_integer(a) and to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)));
      invariant 0 <= to_integer(b) and to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)));
      maintain by {
        have 0u64 < loop(5).iter.len();
        have 1u64 <= loop(5).iter.len() by close() using { 0u64 < loop(5).iter.len(); };
        have loop(5).iter.len() <= 22208u64 by close() using { loop(5).iter.len() <= remainder.len(); remainder.len() <= 3u64; };
        apply(adler_count_tail_step(loop(5).iter.len()));
        have 0 < ((loop(5).iter.len() as u32) as i32) by close() using { 1 <= ((loop(5).iter.len() as u32) as i32); };
       have 1 <= ((loop(5).iter.len() as u32) as i32) by close() using { 0 < ((loop(5).iter.len() as u32) as i32); };
       have 0 <= ((loop(5).iter.len() as u32) as i32) - 1 by close() using { 0 < ((loop(5).iter.len() as u32) as i32); };
       have (((loop(5).iter.len() as u32) as i32)) - 1 <= (((remainder.len() as u32) as i32));
       mark tail_head;
       have 1 <= at(tail_head, ((loop(5).iter.len() as u32) as i32));
       have at(tail_head, ((loop(5).iter.len() as u32) as i32)) <= ((remainder.len() as u32) as i32);
       have at(tail_head, ((loop(5).iter.len() as u32) as i32)) <= ((backing_length as u32) as i32) by close() using { at(tail_head, ((loop(5).iter.len() as u32) as i32)) <= ((remainder.len() as u32) as i32); ((remainder.len() as u32) as i32) <= ((backing_length as u32) as i32); };
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))));
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))));
        have 1u64 <= at(tail_head, loop(5).iter.len());
        have at(tail_head, loop(5).iter.len()) <= remainder.len();
        have backing_length - at(tail_head, loop(5).iter.len()) < backing_length by close() using { 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= backing_length; };
       have truncating_remainder(to_integer(at(tail_head, a)), 65521) == adler_spec_a(bytes.as_ptr(), (((backing_length as u32) as i32) - at(tail_head, ((loop(5).iter.len() as u32) as i32))), old(to_integer((self.a as u32))));
       have truncating_remainder(to_integer(at(tail_head, b)), 65521) == adler_spec_b(bytes.as_ptr(), (((backing_length as u32) as i32) - at(tail_head, ((loop(5).iter.len() as u32) as i32))), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))));
       apply(adler_tail_read_offset(backing_length - backing_length % 4u64, backing_length, remainder.len(), loop(5).iter.len()));
       have at(tail_head, loop(5).iter.as_slice().as_ptr()) == bytes.as_ptr() + (backing_length - at(tail_head, loop(5).iter.len())) by close();
       step_until(loop(5).statement(0).entry);
       have loop(5).iter.len() == at(tail_head, loop(5).iter.len()) - 1u64;
       have at(tail_head, loop(5).iter.len()) <= 2147483647u64 by close() using { at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= 3u64; };
       have loop(5).iter.len() <= 2147483647u64 by close() using { loop(5).iter.len() == at(tail_head, loop(5).iter.len()) - 1u64; 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= 2147483647u64; };
       apply(adler_index_observation(at(tail_head, loop(5).iter.len())));
       apply(adler_index_observation(loop(5).iter.len()));
       apply(adler_count_nonincreasing(at(tail_head, loop(5).iter.len()), loop(5).iter.len(), 1u64));
       apply(integer::uint64_to_integer_less_equal_implies_less_equal(loop(5).iter.len(), at(tail_head, loop(5).iter.len())));
       apply(adler_signed_count_decrease(at(tail_head, loop(5).iter.len()), loop(5).iter.len(), 1u64));
       have defined(at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1) by close();
       apply(integer::int32_subtract_to_integer(at(tail_head, ((loop(5).iter.len() as u32) as i32)), 1));
       have ((loop(5).iter.len() as u32) as i32) == at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1 by close() using {
        to_integer(((loop(5).iter.len() as u32) as i32)) == to_integer(at(tail_head, ((loop(5).iter.len() as u32) as i32))) - 1;
        to_integer(at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1) == to_integer(at(tail_head, ((loop(5).iter.len() as u32) as i32))) - 1;
       };
       have loop(5).iter.len() <= backing_length by close() using { loop(5).iter.len() == at(tail_head, loop(5).iter.len()) - 1u64; 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= backing_length; };
       have 1u64 <= backing_length - loop(5).iter.len() by close() using { loop(5).iter.len() == at(tail_head, loop(5).iter.len()) - 1u64; 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= backing_length; };
       have 0 <= ((loop(5).iter.len() as u32) as i32) by close() using { ((loop(5).iter.len() as u32) as i32) == at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1; 1 <= at(tail_head, ((loop(5).iter.len() as u32) as i32)); at(tail_head, ((loop(5).iter.len() as u32) as i32)) <= ((backing_length as u32) as i32); };
       have at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1 <= ((backing_length as u32) as i32) by close() using { 1 <= at(tail_head, ((loop(5).iter.len() as u32) as i32)); at(tail_head, ((loop(5).iter.len() as u32) as i32)) <= ((backing_length as u32) as i32); };
       have ((loop(5).iter.len() as u32) as i32) <= ((backing_length as u32) as i32) by { rewrite(((loop(5).iter.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1); close(); }
       have defined((((backing_length as u32) as i32)) - (((loop(5).iter.len() as u32) as i32)));
       have 1 <= (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) by close() using { ((loop(5).iter.len() as u32) as i32) == at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1; 1 <= at(tail_head, ((loop(5).iter.len() as u32) as i32)); at(tail_head, ((loop(5).iter.len() as u32) as i32)) <= ((backing_length as u32) as i32); ((backing_length as u32) as i32) <= 22207; };
       apply(integer::int32_subtract_to_integer(((backing_length as u32) as i32), ((loop(5).iter.len() as u32) as i32)));
       have to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1 <= 2147483647 by close() using { to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) == to_integer(((backing_length as u32) as i32)) - to_integer(((loop(5).iter.len() as u32) as i32)); ((backing_length as u32) as i32) <= 22207; 0 <= ((loop(5).iter.len() as u32) as i32); };
       have to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1 >= -2147483648 by close() using { to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) == to_integer(((backing_length as u32) as i32)) - to_integer(((loop(5).iter.len() as u32) as i32)); 1 <= (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)); };
       have defined(((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32))) - 1);
       have to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1 <= 2147483647 and to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1 >= -2147483648 by { all { to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1 <= 2147483647 => { close(); } to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1 >= -2147483648 => { close(); } } }
       apply(integer::int32_subtract_to_integer((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), 1));
       have 0 <= to_integer(((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)) by close() using { to_integer(((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)) == to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1; to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) == to_integer(((backing_length as u32) as i32)) - to_integer(((loop(5).iter.len() as u32) as i32)); 1 <= (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)); };
       have to_integer(((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)) <= 2147483646 by close() using { to_integer(((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)) == to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1; to_integer(((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) == to_integer(((backing_length as u32) as i32)) - to_integer(((loop(5).iter.len() as u32) as i32)); 0 <= ((loop(5).iter.len() as u32) as i32); ((backing_length as u32) as i32) <= 22207; };
       have ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1) == (((backing_length as u32) as i32) - at(tail_head, ((loop(5).iter.len() as u32) as i32))) by {
        apply(adler_tail_index_after_next(((backing_length as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32)), ((loop(5).iter.len() as u32) as i32)));
       }
       have 0 <= ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1) by close() using { ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1) == (((backing_length as u32) as i32) - at(tail_head, ((loop(5).iter.len() as u32) as i32))); 1 <= at(tail_head, ((loop(5).iter.len() as u32) as i32)); at(tail_head, ((loop(5).iter.len() as u32) as i32)) <= ((backing_length as u32) as i32); ((backing_length as u32) as i32) <= 22207; };
       have ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1) <= 2147483646 by close() using { ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1) == (((backing_length as u32) as i32) - at(tail_head, ((loop(5).iter.len() as u32) as i32))); 1 <= at(tail_head, ((loop(5).iter.len() as u32) as i32)); at(tail_head, ((loop(5).iter.len() as u32) as i32)) <= ((backing_length as u32) as i32); ((backing_length as u32) as i32) <= 22207; };
       have (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) == ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1) + 1 by close() using { 0 <= to_integer(((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)); to_integer(((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)) <= 2147483646; ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1) == (((backing_length as u32) as i32) - at(tail_head, ((loop(5).iter.len() as u32) as i32))); ((loop(5).iter.len() as u32) as i32) == at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1; 1 <= at(tail_head, ((loop(5).iter.len() as u32) as i32)); at(tail_head, ((loop(5).iter.len() as u32) as i32)) <= ((backing_length as u32) as i32); ((backing_length as u32) as i32) <= 22207; };
       have backing_length - loop(5).iter.len() - 1u64 == backing_length - at(tail_head, loop(5).iter.len()) by close() using { loop(5).iter.len() == at(tail_head, loop(5).iter.len()) - 1u64; 1u64 <= at(tail_head, loop(5).iter.len()); at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= backing_length; };
       apply(integer::uint64_subtract_to_integer(backing_length, loop(5).iter.len()));
       have at(tail_head, loop(5).iter.len()) <= backing_length by close() using { at(tail_head, loop(5).iter.len()) <= remainder.len(); remainder.len() <= backing_length; };
       apply(integer::uint64_subtract_to_integer(backing_length, at(tail_head, loop(5).iter.len())));
       have to_integer(1u64) <= to_integer(backing_length - loop(5).iter.len()) by close() using { to_integer(backing_length - loop(5).iter.len()) == to_integer(backing_length) - to_integer(loop(5).iter.len()); 1u64 <= backing_length - loop(5).iter.len(); };
       apply(integer::uint64_subtract_to_integer(backing_length - loop(5).iter.len(), 1u64));
       have to_integer(backing_length - loop(5).iter.len() - 1u64) == to_integer(backing_length - at(tail_head, loop(5).iter.len())) by close() using { to_integer(backing_length - loop(5).iter.len()) == to_integer(backing_length) - to_integer(loop(5).iter.len()); to_integer(backing_length - at(tail_head, loop(5).iter.len())) == to_integer(backing_length) - to_integer(at(tail_head, loop(5).iter.len())); to_integer(backing_length - loop(5).iter.len() - 1u64) == to_integer(backing_length - loop(5).iter.len()) - to_integer(1u64); loop(5).iter.len() == at(tail_head, loop(5).iter.len()) - 1u64; };
       have at(tail_head, loop(5).iter.as_slice().as_ptr()) == bytes.as_ptr() + (backing_length - loop(5).iter.len() - 1u64) by close() using { at(tail_head, loop(5).iter.as_slice().as_ptr()) == bytes.as_ptr() + (backing_length - at(tail_head, loop(5).iter.len())); to_integer(backing_length - loop(5).iter.len() - 1u64) == to_integer(backing_length - at(tail_head, loop(5).iter.len())); };
       apply(adler_count_previous_byte_observation(bytes.as_ptr(), backing_length, loop(5).iter.len()));
       have (byte as u32) == (at(tail_head, loop(5).iter.as_slice()[0]) as u32);
       apply(adler_helper_byte_observation(at(tail_head, loop(5).iter.as_slice()[0])));
       have at(tail_head, loop(5).iter.as_slice()[0]) == (at(tail_head, loop(5).iter.as_slice().as_ptr()))[0] by close();
       apply(adler_equal_byte_read(at(tail_head, loop(5).iter.as_slice().as_ptr()), bytes.as_ptr() + (backing_length - loop(5).iter.len() - 1u64), 0));
       have to_integer(byte as u32) == to_integer(((bytes.as_ptr() + (backing_length - loop(5).iter.len() - 1u64))[0] as i32)) by {
        rewrite((byte as u32), (at(tail_head, loop(5).iter.as_slice()[0]) as u32));
        rewrite(to_integer((at(tail_head, loop(5).iter.as_slice()[0]) as u32)), to_integer((at(tail_head, loop(5).iter.as_slice()[0]) as i32)));
        rewrite((at(tail_head, loop(5).iter.as_slice().as_ptr()))[0], (bytes.as_ptr() + (backing_length - loop(5).iter.len() - 1u64))[0]);
        close();
       }
       have to_integer(byte as u32) == to_integer((bytes[((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)] as i32)) by {
        rewrite(to_integer(byte as u32), to_integer(((bytes.as_ptr() + (backing_length - loop(5).iter.len() - 1u64))[0] as i32)));
        close() using { to_integer(((bytes.as_ptr() + (backing_length - loop(5).iter.len() - 1u64))[0] as i32)) == to_integer((bytes[((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)] as i32)); };
       }
       have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes.as_ptr(), ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1), old(to_integer((self.a as u32)))) by { rewrite(((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1), (((backing_length as u32) as i32) - at(tail_head, ((loop(5).iter.len() as u32) as i32)))); close(); }
       have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes.as_ptr(), ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1), (((backing_length as u32) as i32) - at(tail_head, ((loop(5).iter.len() as u32) as i32)))); close(); }
       apply(adler_prefix_a_step_one(bytes.as_ptr(), ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1), old(to_integer((self.a as u32))), to_integer(a)));
       apply(adler_prefix_b_step_one(bytes.as_ptr(), ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))), to_integer(a), to_integer(b)));
       have (byte as u32) <= 255u32;
       have to_integer(byte as u32) <= to_integer(255u32);
       have to_integer(byte as u32) <= 255 by close() using { to_integer(byte as u32) <= to_integer(255u32); };
       apply(adler_tail_iterator_step(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32)), to_integer(a), to_integer(b), to_integer(byte as u32)));
       have a <= 4294967295u32 - (byte as u32);
       mark tail_add_a;
       have to_integer(at(tail_add_a, a)) == to_integer(a) by close();
       have to_integer(at(tail_add_a, b)) == to_integer(b) by close();
       have to_integer(at(tail_add_a, byte as u32)) == to_integer((bytes[((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)] as i32)) by close() using { to_integer(byte as u32) == to_integer((bytes[((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)] as i32)); };
       have truncating_remainder(to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)), 65521) == adler_spec_a(bytes.as_ptr(), (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), old(to_integer((self.a as u32)))) by {
        rewrite((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1) + 1);
        rewrite(to_integer(at(tail_add_a, a)), to_integer(a));
        rewrite(to_integer(at(tail_add_a, byte as u32)), to_integer((bytes[((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)] as i32)));
        close();
       }
       have truncating_remainder(to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)), 65521) == adler_spec_b(bytes.as_ptr(), (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by {
        rewrite((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), ((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1) + 1);
        rewrite(to_integer(at(tail_add_a, b)), to_integer(b));
        rewrite(to_integer(at(tail_add_a, a)), to_integer(a));
        rewrite(to_integer(at(tail_add_a, byte as u32)), to_integer((bytes[((((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)) - 1)] as i32)));
        close();
       }

       have to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) <= 4294967295 by close();
       apply(integer::uint32_add_to_integer(at(tail_add_a, a), at(tail_add_a, byte as u32)));
       step_until(assignment(a, 2).entry); step();
       have a == at(tail_add_a, a) + at(tail_add_a, byte as u32) by close();
       have to_integer(a) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by close();
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1) by close();
       have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes.as_ptr(), (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), old(to_integer((self.a as u32)))) by { rewrite(to_integer(a), to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32))); close(); }
       have to_integer(b) == to_integer(at(tail_add_a, b)) by close();
       have to_integer(b) + to_integer(a) <= 4294967295 by close();
       have to_integer(b) + to_integer(a) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1) by close();
       mark tail_add_b;
       have to_integer(at(tail_add_b, a)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by close() using {
        to_integer(a) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32));
       };
       have to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b)) by close();
       have to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, a)) <= 4294967295 by close();
       apply(integer::uint32_add_to_integer(at(tail_add_b, b), at(tail_add_b, a)));
       have to_integer(a) <= 4294967295 by close();
       apply(integer::uint32_subtract_to_integer(4294967295u32, a));
       have to_integer(4294967295u32 - a) == 4294967295 - to_integer(a) by close();
       have to_integer(b) <= to_integer(4294967295u32 - a) by close() using {
        to_integer(b) + to_integer(a) <= 4294967295;
        to_integer(4294967295u32 - a) == 4294967295 - to_integer(a);
       };
       step_until(assignment(b, 6).entry); step();
       have b == at(tail_add_b, b) + at(tail_add_b, a) by close();
       have to_integer(b) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, a)) by close();
       have to_integer(b) == to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32)) by close() using {
        to_integer(b) == to_integer(at(tail_add_b, b)) + to_integer(at(tail_add_b, a));
        to_integer(at(tail_add_b, a)) == to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32));
        to_integer(at(tail_add_b, b)) == to_integer(at(tail_add_a, b));
       };
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1) by close();
       have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes.as_ptr(), (((backing_length as u32) as i32) - ((loop(5).iter.len() as u32) as i32)), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), to_integer(at(tail_add_a, b)) + to_integer(at(tail_add_a, a)) + to_integer(at(tail_add_a, byte as u32))); close(); }
       step_until(loop.back_edge);
        have to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len()) - 1u64);
        have to_integer(((loop(5).iter.len() as u32) as i32)) == to_integer(at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1) by { rewrite(to_integer(loop(5).iter.len()), to_integer(at(tail_head, loop(5).iter.len()) - 1u64)); close(); }
       apply(adler_tail_remaining_progress(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))));
       have adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)) == adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1 by { rewrite(to_integer(((loop(5).iter.len() as u32) as i32)), to_integer(at(tail_head, ((loop(5).iter.len() as u32) as i32)) - 1)); close(); }
       have to_integer(a) <= adler_tail_a_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)), adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1); close(); }
       have to_integer(b) <= adler_tail_b_ceiling(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32))) by { rewrite(adler_tail_consumed(((remainder.len() as u32) as i32), ((loop(5).iter.len() as u32) as i32)), adler_tail_consumed(((remainder.len() as u32) as i32), at(tail_head, ((loop(5).iter.len() as u32) as i32))) + 1); close(); }
       have 0 <= to_integer(a); have to_integer(a) <= 4294967295; have 0 <= to_integer(b); have to_integer(b) <= 4294967295;
       have 0 <= ((loop(5).iter.len() as u32) as i32) and ((loop(5).iter.len() as u32) as i32) <= ((remainder.len() as u32) as i32);
       have to_integer(at(tail_head, loop(5).iter.len())) <= to_integer(remainder.len()) by close();
       have 1 <= to_integer(at(tail_head, loop(5).iter.len())) by close();
       apply(integer::uint64_subtract_to_integer(at(tail_head, loop(5).iter.len()), 1u64));
       have to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len())) - 1 by close();
       have to_integer(loop(5).iter.len()) <= to_integer(remainder.len()) by close() using {
        to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len())) - 1;
        to_integer(at(tail_head, loop(5).iter.len())) <= to_integer(remainder.len());
       };
       have loop(5).iter.len() <= remainder.len() by close();
       have at(tail_head, loop(5).iter.len()) <= backing_length by close();
       have loop(5).iter.len() <= backing_length by close();
       apply(integer::uint64_subtract_to_integer(backing_length, at(tail_head, loop(5).iter.len())));
       apply(integer::uint64_subtract_to_integer(backing_length, loop(5).iter.len()));
       have to_integer((backing_length - at(tail_head, loop(5).iter.len()))) + 1 <= 18446744073709551615 by close() using {
        to_integer((backing_length - at(tail_head, loop(5).iter.len()))) == to_integer(backing_length) - to_integer(at(tail_head, loop(5).iter.len()));
        to_integer(backing_length) <= 18446744073709551615;
        1 <= to_integer(at(tail_head, loop(5).iter.len()));
       };
       apply(integer::uint64_add_to_integer((backing_length - at(tail_head, loop(5).iter.len())), 1u64));
       have to_integer((backing_length - loop(5).iter.len())) == to_integer((backing_length - at(tail_head, loop(5).iter.len())) + 1u64) by close() using {
        to_integer((backing_length - loop(5).iter.len())) == to_integer(backing_length) - to_integer(loop(5).iter.len());
        to_integer((backing_length - at(tail_head, loop(5).iter.len())) + 1u64) == to_integer((backing_length - at(tail_head, loop(5).iter.len()))) + 1;
        to_integer((backing_length - at(tail_head, loop(5).iter.len()))) == to_integer(backing_length) - to_integer(at(tail_head, loop(5).iter.len()));
        to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len())) - 1;
       };
       have loop(5).iter.len() < at(tail_head, loop(5).iter.len()) by close() using { to_integer(loop(5).iter.len()) == to_integer(at(tail_head, loop(5).iter.len())) - 1; };
       have loop(5).iter.as_slice().as_ptr() == byte_offset(at(tail_head, loop(5).iter.as_slice().as_ptr()), 1) by close();
       apply(adler_uint64_pointer_association(bytes.as_ptr(), (backing_length - at(tail_head, loop(5).iter.len())), 1u64));
       have loop(5).iter.as_slice().as_ptr() == bytes.as_ptr() + (backing_length - loop(5).iter.len()) by {
        rewrite(loop(5).iter.as_slice().as_ptr(), byte_offset(at(tail_head, loop(5).iter.as_slice().as_ptr()), 1));
        rewrite(at(tail_head, loop(5).iter.as_slice().as_ptr()), bytes.as_ptr() + (backing_length - at(tail_head, loop(5).iter.len())));
        rewrite(to_integer((backing_length - loop(5).iter.len())), to_integer((backing_length - at(tail_head, loop(5).iter.len())) + 1u64));
        close();
       }
       have defined((((backing_length as u32) as i32)) - (((loop(5).iter.len() as u32) as i32)));
      }
     }

     step_until(statement(22).entry);
     have at(loop(5).exit, loop(5).iter.len()) == 0u64 by close() using { not (0u64 < at(loop(5).exit, loop(5).iter.len())); };
     have at(loop(5).exit, ((loop(5).iter.len() as u32) as i32)) == 0 by { rewrite(at(loop(5).exit, loop(5).iter.len()), 0u64); close(); }
     have truncating_remainder(to_integer(at(loop(5).exit, a)), 65521) == adler_spec_a(bytes.as_ptr(), (((backing_length as u32) as i32) - at(loop(5).exit, ((loop(5).iter.len() as u32) as i32))), old(to_integer((self.a as u32)))) by close();
     have to_integer(a) == to_integer(at(loop(5).exit, a)) by close();
     have to_integer(((backing_length as u32) as i32)) == to_integer((((backing_length as u32) as i32) - at(loop(5).exit, ((loop(5).iter.len() as u32) as i32)))) by { rewrite(at(loop(5).exit, ((loop(5).iter.len() as u32) as i32)), 0); close(); }
     have truncating_remainder(to_integer(a), 65521) == adler_spec_a(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32)))) by { rewrite(to_integer(a), to_integer(at(loop(5).exit, a))); rewrite(to_integer(((backing_length as u32) as i32)), to_integer((((backing_length as u32) as i32) - at(loop(5).exit, ((loop(5).iter.len() as u32) as i32))))); close(); }
     have truncating_remainder(to_integer(at(loop(5).exit, b)), 65521) == adler_spec_b(bytes.as_ptr(), (((backing_length as u32) as i32) - at(loop(5).exit, ((loop(5).iter.len() as u32) as i32))), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by close();
     have to_integer(b) == to_integer(at(loop(5).exit, b)) by close();
     have to_integer(((backing_length as u32) as i32)) == to_integer((((backing_length as u32) as i32) - at(loop(5).exit, ((loop(5).iter.len() as u32) as i32)))) by { rewrite(at(loop(5).exit, ((loop(5).iter.len() as u32) as i32)), 0); close(); }
     have truncating_remainder(to_integer(b), 65521) == adler_spec_b(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) by { rewrite(to_integer(b), to_integer(at(loop(5).exit, b))); rewrite(to_integer(((backing_length as u32) as i32)), to_integer((((backing_length as u32) as i32) - at(loop(5).exit, ((loop(5).iter.len() as u32) as i32))))); close(); }
     have forall (k: int32) { 0 <= k and k < ((backing_length as u32) as i32) implies bytes[k] == old(bytes[k]) } by close();
     apply(adler_index_observation(backing_length));
     apply(adler_spec_extensional(bytes.as_ptr(), old(bytes.as_ptr()), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
     have adler_spec_a(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32)))) == old(adler_spec_a(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))))) by close() using { adler_spec_a(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32)))) == adler_spec_a(old(bytes.as_ptr()), ((backing_length as u32) as i32), old(to_integer((self.a as u32)))); };
     have adler_spec_b(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == old(adler_spec_b(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by close() using { adler_spec_b(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))) == adler_spec_b(old(bytes.as_ptr()), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))); };
     have truncating_remainder(to_integer(a), 65521) == old(adler_spec_a(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))))) by {
      rewrite(truncating_remainder(to_integer(a), 65521), adler_spec_a(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32)))));
      close();
     }
     have truncating_remainder(to_integer(b), 65521) == old(adler_spec_b(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by {
      rewrite(truncating_remainder(to_integer(b), 65521), adler_spec_b(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
      close();
     }
     mark tail_done;
     have truncating_remainder(to_integer(at(tail_done, a)), 65521) == old(adler_spec_a(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))))) by close() using { truncating_remainder(to_integer(a), 65521) == old(adler_spec_a(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))))); };
     have truncating_remainder(to_integer(at(tail_done, b)), 65521) == old(adler_spec_b(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by close() using { truncating_remainder(to_integer(b), 65521) == old(adler_spec_b(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };

     apply(integer::uint32_remainder_to_integer(at(tail_done, a), 65521u32));
     have to_integer((at(tail_done, a) % 65521u32)) == truncating_remainder(to_integer(at(tail_done, a)), 65521) by close();
     have to_integer((at(tail_done, a) % 65521u32)) == old(adler_spec_a(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))))) by { rewrite(to_integer((at(tail_done, a) % 65521u32)), truncating_remainder(to_integer(at(tail_done, a)), 65521)); close(); }
     have (at(tail_done, a) % 65521u32) < 65521u32;
     have 0 <= to_integer((at(tail_done, a) % 65521u32));
     have to_integer((at(tail_done, a) % 65521u32)) <= 4294967295;
     have to_integer((at(tail_done, a) % 65521u32)) < 65521 by close() using { to_integer((at(tail_done, a) % 65521u32)) < to_integer(65521u32); };

     apply(integer::uint32_remainder_to_integer(at(tail_done, b), 65521u32));
     have to_integer((at(tail_done, b) % 65521u32)) == truncating_remainder(to_integer(at(tail_done, b)), 65521) by close();
     have to_integer((at(tail_done, b) % 65521u32)) == old(adler_spec_b(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by { rewrite(to_integer((at(tail_done, b) % 65521u32)), truncating_remainder(to_integer(at(tail_done, b)), 65521)); close(); }
     have (at(tail_done, b) % 65521u32) < 65521u32;
     have 0 <= to_integer((at(tail_done, b) % 65521u32));
     have to_integer((at(tail_done, b) % 65521u32)) <= 4294967295;
     have to_integer((at(tail_done, b) % 65521u32)) < 65521 by close() using { to_integer((at(tail_done, b) % 65521u32)) < to_integer(65521u32); };

     step_until(function.exit);
     have statement(22).call(0).result == 65521u32 by close();
     have self.a == ((at(tail_done, a) % statement(22).call(0).result) as u16) by close();
     have self.a == ((at(tail_done, a) % 65521u32) as u16) by { rewrite(self.a, ((at(tail_done, a) % statement(22).call(0).result) as u16)); rewrite(statement(22).call(0).result, 65521u32); close(); }
     apply(adler_narrow_residue((at(tail_done, a) % 65521u32)));
     have to_integer(self.a) == to_integer((at(tail_done, a) % 65521u32)) by {
      rewrite(self.a, ((at(tail_done, a) % 65521u32) as u16));
      close();
     }
     have to_integer(self.a) == old(adler_spec_a(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))))) by { rewrite(to_integer(self.a), to_integer((at(tail_done, a) % 65521u32))); close(); }
     have to_integer((at(tail_done, a) % 65521u32)) < 65521;
     have to_integer(self.a) < 65521 by { rewrite(to_integer(self.a), to_integer((at(tail_done, a) % 65521u32))); close(); }
     have statement(23).call(0).result == 65521u32 by close();
     have self.b == ((at(tail_done, b) % statement(23).call(0).result) as u16) by close();
     have self.b == ((at(tail_done, b) % 65521u32) as u16) by { rewrite(self.b, ((at(tail_done, b) % statement(23).call(0).result) as u16)); rewrite(statement(23).call(0).result, 65521u32); close(); }
     apply(adler_narrow_residue((at(tail_done, b) % 65521u32)));
     have to_integer(self.b) == to_integer((at(tail_done, b) % 65521u32)) by {
      rewrite(self.b, ((at(tail_done, b) % 65521u32) as u16));
      close();
     }
     have to_integer(self.b) == old(adler_spec_b(bytes.as_ptr(), ((backing_length as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by { rewrite(to_integer(self.b), to_integer((at(tail_done, b) % 65521u32))); close(); }
     have to_integer((at(tail_done, b) % 65521u32)) < 65521;
     have to_integer(self.b) < 65521 by { rewrite(to_integer(self.b), to_integer((at(tail_done, b) % 65521u32))); close(); }
     apply(adler_uint16_below_mod(self.a));
     apply(adler_uint16_below_mod(self.b));
     have old(((bytes.len() as u32) as i32)) == ((backing_length as u32) as i32) by close();
     have to_integer(self.a) == old(adler_spec_a(bytes.as_ptr(), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))) by {
      rewrite(old(((bytes.len() as u32) as i32)), ((backing_length as u32) as i32));
      close();
     }
     have to_integer(self.b) == old(adler_spec_b(bytes.as_ptr(), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))) by {
      rewrite(old(((bytes.len() as u32) as i32)), ((backing_length as u32) as i32));
      close();
     }
     // Return both owned fields before discharging the checksum claims.
     close() using {};
     close() using {};
     close() using { self.a < 65521; };
     close() using { self.b < 65521; };
     close() using { to_integer(self.a) == old(adler_spec_a(bytes.as_ptr(), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))))); };
     close() using { to_integer(self.b) == old(adler_spec_b(bytes.as_ptr(), ((bytes.len() as u32) as i32), old(to_integer((self.a as u32))), old(to_integer((self.b as u32))))); };
    }
}
