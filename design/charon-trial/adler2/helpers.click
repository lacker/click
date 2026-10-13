verifying "src/lib.rs";

theorem adler_helper_byte_observation(value: uint8) {
 ensures to_integer((value as u32)) == to_integer((value as i32)) by {
  have 0 <= (value as i32);
  have (value as i32) <= 255;
  apply(int32_less_equal_to_integer(0, (value as i32)));
  apply(int32_less_equal_to_integer((value as i32), 255));
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer((value as i32)) => 0 <= to_integer((value as i32));
   premise 1: to_integer((value as i32)) <= 255 => to_integer((value as i32)) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((value as u32)) == to_integer((value as i32));
   conclusion 0;
  }
 }
}

impl adler2::algo::U32X4 {
    fn from(bytes: &[u8]) -> adler2::algo::U32X4 {
        requires bytes.len() >= 4u64;
        views bytes[0..4];
        ensures result.0[0] == bytes[0];
        ensures result.0[1] == bytes[1];
        ensures result.0[2] == bytes[2];
        ensures result.0[3] == bytes[3];
        ensures result.0[0] <= 255u32;
        ensures result.0[1] <= 255u32;
        ensures result.0[2] <= 255u32;
        ensures result.0[3] <= 255u32;
        ensures 0 <= to_integer(result.0[0]);
        ensures to_integer(result.0[0]) <= 255;
        ensures 0 <= to_integer(result.0[1]);
        ensures to_integer(result.0[1]) <= 255;
        ensures 0 <= to_integer(result.0[2]);
        ensures to_integer(result.0[2]) <= 255;
        ensures 0 <= to_integer(result.0[3]);
        ensures to_integer(result.0[3]) <= 255;
        ensures to_integer(result.0[0]) == old(to_integer((bytes[0] as i32)));
        ensures to_integer(result.0[1]) == old(to_integer((bytes[1] as i32)));
        ensures to_integer(result.0[2]) == old(to_integer((bytes[2] as i32)));
        ensures to_integer(result.0[3]) == old(to_integer((bytes[3] as i32)));
    } by {
        apply(adler_helper_byte_observation(bytes[0]));
        apply(adler_helper_byte_observation(bytes[1]));
        apply(adler_helper_byte_observation(bytes[2]));
        apply(adler_helper_byte_observation(bytes[3]));
        execute();
        apply(uint32_to_integer_bounds(result.0[0]));
        apply(uint32_less_equal_to_integer(result.0[0], 255u32));
        apply(uint32_to_integer_bounds(result.0[1]));
        apply(uint32_less_equal_to_integer(result.0[1], 255u32));
        apply(uint32_to_integer_bounds(result.0[2]));
        apply(uint32_less_equal_to_integer(result.0[2], 255u32));
        apply(uint32_to_integer_bounds(result.0[3]));
        apply(uint32_less_equal_to_integer(result.0[3], 255u32));
        have result.0[0] == old((bytes[0] as u32));
        have to_integer(result.0[0]) == old(to_integer((bytes[0] as i32))) by { rewrite(result.0[0] == old((bytes[0] as u32))); assumption(); }
        have result.0[1] == old((bytes[1] as u32));
        have to_integer(result.0[1]) == old(to_integer((bytes[1] as i32))) by { rewrite(result.0[1] == old((bytes[1] as u32))); assumption(); }
        have result.0[2] == old((bytes[2] as u32));
        have to_integer(result.0[2]) == old(to_integer((bytes[2] as i32))) by { rewrite(result.0[2] == old((bytes[2] as u32))); assumption(); }
        have result.0[3] == old((bytes[3] as u32));
        have to_integer(result.0[3]) == old(to_integer((bytes[3] as i32))) by { rewrite(result.0[3] == old((bytes[3] as u32))); assumption(); }
        // Establish the byte ranges independently of the ensures clauses, then
        // close from those checked witnesses so false bounds fail without search.
        have 255u32 >= result.0[0];
        have to_integer(result.0[0]) >= 0;
        have 255 >= to_integer(result.0[0]);
        have 255u32 >= result.0[1];
        have to_integer(result.0[1]) >= 0;
        have 255 >= to_integer(result.0[1]);
        have 255u32 >= result.0[2];
        have to_integer(result.0[2]) >= 0;
        have 255 >= to_integer(result.0[2]);
        have 255u32 >= result.0[3];
        have to_integer(result.0[3]) >= 0;
        have 255 >= to_integer(result.0[3]);
        simp() using {
            result.0[0] == old((bytes[0] as u32));
            to_integer(result.0[0]) == old(to_integer((bytes[0] as i32)));
            255u32 >= result.0[0];
            to_integer(result.0[0]) >= 0;
            255 >= to_integer(result.0[0]);
            result.0[1] == old((bytes[1] as u32));
            to_integer(result.0[1]) == old(to_integer((bytes[1] as i32)));
            255u32 >= result.0[1];
            to_integer(result.0[1]) >= 0;
            255 >= to_integer(result.0[1]);
            result.0[2] == old((bytes[2] as u32));
            to_integer(result.0[2]) == old(to_integer((bytes[2] as i32)));
            255u32 >= result.0[2];
            to_integer(result.0[2]) >= 0;
            255 >= to_integer(result.0[2]);
            result.0[3] == old((bytes[3] as u32));
            to_integer(result.0[3]) == old(to_integer((bytes[3] as i32)));
            255u32 >= result.0[3];
            to_integer(result.0[3]) >= 0;
            255 >= to_integer(result.0[3]);
        }
    }
}

impl AddAssign<adler2::algo::U32X4> for adler2::algo::U32X4 {
    fn add_assign(&mut self, other: adler2::algo::U32X4) {
        requires to_integer(self.0[0]) + to_integer(other.0[0]) <= 4294967295;
        requires to_integer(self.0[1]) + to_integer(other.0[1]) <= 4294967295;
        requires to_integer(self.0[2]) + to_integer(other.0[2]) <= 4294967295;
        requires to_integer(self.0[3]) + to_integer(other.0[3]) <= 4294967295;
        owns self.0[0..4];
        ensures self.0[0] == old(self.0[0]) + other.0[0];
        ensures self.0[1] == old(self.0[1]) + other.0[1];
        ensures self.0[2] == old(self.0[2]) + other.0[2];
        ensures self.0[3] == old(self.0[3]) + other.0[3];
        ensures to_integer(self.0[0]) == to_integer(old(self.0[0])) + to_integer(other.0[0]);
        ensures 0 <= to_integer(self.0[0]);
        ensures to_integer(self.0[1]) == to_integer(old(self.0[1])) + to_integer(other.0[1]);
        ensures 0 <= to_integer(self.0[1]);
        ensures to_integer(self.0[2]) == to_integer(old(self.0[2])) + to_integer(other.0[2]);
        ensures 0 <= to_integer(self.0[2]);
        ensures to_integer(self.0[3]) == to_integer(old(self.0[3])) + to_integer(other.0[3]);
        ensures 0 <= to_integer(self.0[3]);
    } by {
        apply(uint32_widened_add_guard_by_integer_bound(self.0[0], other.0[0]));
        apply(uint32_widened_add_guard_by_integer_bound(self.0[1], other.0[1]));
        apply(uint32_widened_add_guard_by_integer_bound(self.0[2], other.0[2]));
        apply(uint32_widened_add_guard_by_integer_bound(self.0[3], other.0[3]));
        execute();
        apply(uint32_add_to_integer(old(self.0[0]), other.0[0]));
        apply(uint32_to_integer_bounds(self.0[0]));
        apply(uint32_add_to_integer(old(self.0[1]), other.0[1]));
        apply(uint32_to_integer_bounds(self.0[1]));
        apply(uint32_add_to_integer(old(self.0[2]), other.0[2]));
        apply(uint32_to_integer_bounds(self.0[2]));
        apply(uint32_add_to_integer(old(self.0[3]), other.0[3]));
        apply(uint32_to_integer_bounds(self.0[3]));
        simp();
    }
}

impl RemAssign<u32> for adler2::algo::U32X4 {
    fn rem_assign(&mut self, quotient: u32) {
        requires quotient != 0u32;
        owns self.0[0..4];
        ensures self.0[0] == old(self.0[0]) % quotient;
        ensures self.0[1] == old(self.0[1]) % quotient;
        ensures self.0[2] == old(self.0[2]) % quotient;
        ensures self.0[3] == old(self.0[3]) % quotient;
        ensures to_integer(self.0[0]) == truncating_remainder(to_integer(old(self.0[0])), to_integer(quotient));
        ensures to_integer(self.0[1]) == truncating_remainder(to_integer(old(self.0[1])), to_integer(quotient));
        ensures to_integer(self.0[2]) == truncating_remainder(to_integer(old(self.0[2])), to_integer(quotient));
        ensures to_integer(self.0[3]) == truncating_remainder(to_integer(old(self.0[3])), to_integer(quotient));
        ensures self.0[0] < quotient;
        ensures 0 <= to_integer(self.0[0]);
        ensures to_integer(self.0[0]) < to_integer(quotient);
        ensures self.0[1] < quotient;
        ensures 0 <= to_integer(self.0[1]);
        ensures to_integer(self.0[1]) < to_integer(quotient);
        ensures self.0[2] < quotient;
        ensures 0 <= to_integer(self.0[2]);
        ensures to_integer(self.0[2]) < to_integer(quotient);
        ensures self.0[3] < quotient;
        ensures 0 <= to_integer(self.0[3]);
        ensures to_integer(self.0[3]) < to_integer(quotient);
        ensures old(self.0[0]) < quotient implies self.0[0] == old(self.0[0]);
        ensures old(self.0[1]) < quotient implies self.0[1] == old(self.0[1]);
        ensures old(self.0[2]) < quotient implies self.0[2] == old(self.0[2]);
        ensures old(self.0[3]) < quotient implies self.0[3] == old(self.0[3]);
    } by {
        apply(uint32_nonzero_to_integer(quotient));
        apply(uint32_remainder_to_integer(self.0[0], quotient));
        apply(uint32_remainder_to_integer(self.0[1], quotient));
        apply(uint32_remainder_to_integer(self.0[2], quotient));
        apply(uint32_remainder_to_integer(self.0[3], quotient));
        execute();
        have self.0[0] == old(self.0[0]) % quotient;
        have to_integer(self.0[0]) == truncating_remainder(to_integer(old(self.0[0])), to_integer(quotient)) by {
            rewrite(self.0[0] == old(self.0[0]) % quotient);
            assumption();
        }
        have self.0[1] == old(self.0[1]) % quotient;
        have to_integer(self.0[1]) == truncating_remainder(to_integer(old(self.0[1])), to_integer(quotient)) by {
            rewrite(self.0[1] == old(self.0[1]) % quotient);
            assumption();
        }
        have self.0[2] == old(self.0[2]) % quotient;
        have to_integer(self.0[2]) == truncating_remainder(to_integer(old(self.0[2])), to_integer(quotient)) by {
            rewrite(self.0[2] == old(self.0[2]) % quotient);
            assumption();
        }
        have self.0[3] == old(self.0[3]) % quotient;
        have to_integer(self.0[3]) == truncating_remainder(to_integer(old(self.0[3])), to_integer(quotient)) by {
            rewrite(self.0[3] == old(self.0[3]) % quotient);
            assumption();
        }
        apply(uint32_remainder_less_than_divisor(old(self.0[0]), quotient));
        have self.0[0] < quotient;
        apply(uint32_to_integer_bounds(self.0[0]));
        apply(uint32_less_than_to_integer(self.0[0], quotient));
        apply(uint32_remainder_less_than_divisor(old(self.0[1]), quotient));
        have self.0[1] < quotient;
        apply(uint32_to_integer_bounds(self.0[1]));
        apply(uint32_less_than_to_integer(self.0[1], quotient));
        apply(uint32_remainder_less_than_divisor(old(self.0[2]), quotient));
        have self.0[2] < quotient;
        apply(uint32_to_integer_bounds(self.0[2]));
        apply(uint32_less_than_to_integer(self.0[2], quotient));
        apply(uint32_remainder_less_than_divisor(old(self.0[3]), quotient));
        have self.0[3] < quotient;
        apply(uint32_to_integer_bounds(self.0[3]));
        apply(uint32_less_than_to_integer(self.0[3], quotient));
        have old(self.0[0]) < quotient implies self.0[0] == old(self.0[0]) by {
            if old(self.0[0]) < quotient {
                apply(uint32_less_than_divisor_implies_remainder_is_value(old(self.0[0]), quotient));
                simp();
            } else { simp(); }
        }
        have old(self.0[1]) < quotient implies self.0[1] == old(self.0[1]) by {
            if old(self.0[1]) < quotient {
                apply(uint32_less_than_divisor_implies_remainder_is_value(old(self.0[1]), quotient));
                simp();
            } else { simp(); }
        }
        have old(self.0[2]) < quotient implies self.0[2] == old(self.0[2]) by {
            if old(self.0[2]) < quotient {
                apply(uint32_less_than_divisor_implies_remainder_is_value(old(self.0[2]), quotient));
                simp();
            } else { simp(); }
        }
        have old(self.0[3]) < quotient implies self.0[3] == old(self.0[3]) by {
            if old(self.0[3]) < quotient {
                apply(uint32_less_than_divisor_implies_remainder_is_value(old(self.0[3]), quotient));
                simp();
            } else { simp(); }
        }
        simp();
    }
}

impl MulAssign<u32> for adler2::algo::U32X4 {
    fn mul_assign(&mut self, rhs: u32) {
        requires rhs == 0u32 or self.0[0] <= 4294967295u32 / rhs;
        requires rhs == 0u32 or self.0[1] <= 4294967295u32 / rhs;
        requires rhs == 0u32 or self.0[2] <= 4294967295u32 / rhs;
        requires rhs == 0u32 or self.0[3] <= 4294967295u32 / rhs;
        owns self.0[0..4];
        ensures self.0[0] == old(self.0[0]) * rhs;
        ensures self.0[1] == old(self.0[1]) * rhs;
        ensures self.0[2] == old(self.0[2]) * rhs;
        ensures self.0[3] == old(self.0[3]) * rhs;
        ensures to_integer(self.0[0]) == to_integer(old(self.0[0])) * to_integer(rhs);
        ensures 0 <= to_integer(self.0[0]);
        ensures to_integer(self.0[0]) <= 4294967295;
        ensures to_integer(self.0[1]) == to_integer(old(self.0[1])) * to_integer(rhs);
        ensures 0 <= to_integer(self.0[1]);
        ensures to_integer(self.0[1]) <= 4294967295;
        ensures to_integer(self.0[2]) == to_integer(old(self.0[2])) * to_integer(rhs);
        ensures 0 <= to_integer(self.0[2]);
        ensures to_integer(self.0[2]) <= 4294967295;
        ensures to_integer(self.0[3]) == to_integer(old(self.0[3])) * to_integer(rhs);
        ensures 0 <= to_integer(self.0[3]);
        ensures to_integer(self.0[3]) <= 4294967295;
    } by {
        execute();
        apply(uint32_multiply_to_integer(old(self.0[0]), rhs));
        apply(uint32_to_integer_bounds(self.0[0]));
        apply(uint32_multiply_to_integer(old(self.0[1]), rhs));
        apply(uint32_to_integer_bounds(self.0[1]));
        apply(uint32_multiply_to_integer(old(self.0[2]), rhs));
        apply(uint32_to_integer_bounds(self.0[2]));
        apply(uint32_multiply_to_integer(old(self.0[3]), rhs));
        apply(uint32_to_integer_bounds(self.0[3]));
        simp();
    }
}

// Empty-input boundary of the original, locked Adler32::compute body.
// The preceding helper bodies and both constant getters are checked here too.
impl adler2::Adler32 {
    fn compute(&mut self, bytes: &[u8]) {
     requires bytes.len() == 0u64;
     requires self.a == 1;
     requires self.b == 0;
     owns self.a;
     owns self.b;
     views bytes[0..0];
     ensures self.a == 1;
     ensures self.b == 0;
    } by {
     // The empty chunk iterators execute no body. Prove the scalar reduction
     // from its checked transition before following lane recombination.
     execute_until(assignment(b, 0)); step();
     have b == 0u32;
     execute_until(assignment(b, 3));
     have b == 0u32;
     have __rust_mir_78 == 0u64;
     step();
     have b == 0u32;
     execute_until(assignment(b, 4));
     mark scalar_mod;
     have at(scalar_mod, b) == 0u32;
     step();
     have b == at(scalar_mod, b) % 65521u32;
     have b == 0u32 by {
     rewrite(b == at(scalar_mod, b) % 65521u32);
     rewrite(at(scalar_mod, b) == 0u32);
     simp();
     }
     // Marks bind the operands before each original lane update. __rust_checked
     // locals are the adapter's actual captured call/arithmetic operands, not
     // proof counters. These names are checked against the frozen import.
     execute_until(assignment(__rust_mir_94, 0));
     mark add_lane_1;
     have at(add_lane_1, b_vec.0[1]) == 0u32;
     have at(add_lane_1, __rust_mir_89) == 65521u32;
     step();
     mark stored_lane_1;
     have __rust_mir_94 == at(add_lane_1, b_vec.0[1]) + at(add_lane_1, __rust_mir_89);
     have at(stored_lane_1, __rust_mir_94) == 65521u32 by {
      rewrite(__rust_mir_94 == at(add_lane_1, b_vec.0[1]) + at(add_lane_1, __rust_mir_89));
      rewrite(at(add_lane_1, b_vec.0[1]) == 0u32);
      rewrite(at(add_lane_1, __rust_mir_89) == 65521u32);
      simp();
     }
     execute_until(assignment(__rust_mir_98, 0));
     have b_vec.0[1] == at(stored_lane_1, __rust_mir_94);
     have b_vec.0[1] == 65521u32 by {
      rewrite(b_vec.0[1] == at(stored_lane_1, __rust_mir_94));
      rewrite(at(stored_lane_1, __rust_mir_94) == 65521u32);
      simp();
     }
     execute_until(assignment(__rust_mir_99, 0));
     mark subtract_double;
     have at(subtract_double, __rust_checked_53) == 65521u32;
     have at(subtract_double, __rust_checked_54) == 0u32;
     step();
     have __rust_mir_99 == at(subtract_double, __rust_checked_53) - at(subtract_double, __rust_checked_54);
     have __rust_mir_99 == 65521u32 by {
      rewrite(__rust_mir_99 == at(subtract_double, __rust_checked_53) - at(subtract_double, __rust_checked_54));
      rewrite(at(subtract_double, __rust_checked_53) == 65521u32);
      rewrite(at(subtract_double, __rust_checked_54) == 0u32);
      simp();
     }
     execute_until(assignment(__rust_mir_100, 0));
     mark double_lane;
     have at(double_lane, __rust_mir_96) == 65521u32;
     step();
     have __rust_mir_100 == at(double_lane, __rust_mir_96) * 2u32;
     have __rust_mir_100 == 131042u32 by {
      rewrite(__rust_mir_100 == at(double_lane, __rust_mir_96) * 2u32);
      rewrite(at(double_lane, __rust_mir_96) == 65521u32);
      simp();
     }
     execute_until(assignment(__rust_mir_102, 0));
     mark add_lane_2;
     have at(add_lane_2, b_vec.0[2]) == 0u32;
     have at(add_lane_2, __rust_mir_95) == 131042u32;
     step();
     mark stored_lane_2;
     have __rust_mir_102 == at(add_lane_2, b_vec.0[2]) + at(add_lane_2, __rust_mir_95);
     have at(stored_lane_2, __rust_mir_102) == 131042u32 by {
      rewrite(__rust_mir_102 == at(add_lane_2, b_vec.0[2]) + at(add_lane_2, __rust_mir_95));
      rewrite(at(add_lane_2, b_vec.0[2]) == 0u32);
      rewrite(at(add_lane_2, __rust_mir_95) == 131042u32);
      simp();
     }
     execute_until(assignment(__rust_mir_106, 0));
     have b_vec.0[2] == at(stored_lane_2, __rust_mir_102);
     have b_vec.0[2] == 131042u32 by {
      rewrite(b_vec.0[2] == at(stored_lane_2, __rust_mir_102));
      rewrite(at(stored_lane_2, __rust_mir_102) == 131042u32);
      simp();
     }
     execute_until(assignment(__rust_mir_107, 0));
     mark subtract_triple;
     have at(subtract_triple, __rust_checked_64) == 65521u32;
     have at(subtract_triple, __rust_checked_65) == 0u32;
     step();
     have __rust_mir_107 == at(subtract_triple, __rust_checked_64) - at(subtract_triple, __rust_checked_65);
     have __rust_mir_107 == 65521u32 by {
      rewrite(__rust_mir_107 == at(subtract_triple, __rust_checked_64) - at(subtract_triple, __rust_checked_65));
      rewrite(at(subtract_triple, __rust_checked_64) == 65521u32);
      rewrite(at(subtract_triple, __rust_checked_65) == 0u32);
      simp();
     }
     execute_until(assignment(__rust_mir_108, 0));
     mark triple_lane;
     have at(triple_lane, __rust_mir_104) == 65521u32;
     step();
     have __rust_mir_108 == at(triple_lane, __rust_mir_104) * 3u32;
     have __rust_mir_108 == 196563u32 by {
      rewrite(__rust_mir_108 == at(triple_lane, __rust_mir_104) * 3u32);
      rewrite(at(triple_lane, __rust_mir_104) == 65521u32);
      simp();
     }
     execute_until(assignment(__rust_mir_110, 0));
     mark add_lane_3;
     have at(add_lane_3, b_vec.0[3]) == 0u32;
     have at(add_lane_3, __rust_mir_103) == 196563u32;
     step();
     mark stored_lane_3;
     have __rust_mir_110 == at(add_lane_3, b_vec.0[3]) + at(add_lane_3, __rust_mir_103);
     have at(stored_lane_3, __rust_mir_110) == 196563u32 by {
      rewrite(__rust_mir_110 == at(add_lane_3, b_vec.0[3]) + at(add_lane_3, __rust_mir_103));
      rewrite(at(add_lane_3, b_vec.0[3]) == 0u32);
      rewrite(at(add_lane_3, __rust_mir_103) == 196563u32);
      simp();
     }
     execute_until(assignment(__rust_mir_113, 0));
     have b_vec.0[3] == at(stored_lane_3, __rust_mir_110);
     have b_vec.0[3] == 196563u32 by {
      rewrite(b_vec.0[3] == at(stored_lane_3, __rust_mir_110));
      rewrite(at(stored_lane_3, __rust_mir_110) == 196563u32);
      simp();
     }
     execute_until(loop(3));
     have a == 1u32;
     have b == 0u32;
     have a_vec.0[0] == 0u32;
     have a_vec.0[1] == 0u32;
     have a_vec.0[2] == 0u32;
     have a_vec.0[3] == 0u32;
     have b_vec.0[0] == 0u32;
     have b_vec.0[1] == 65521u32;
     have b_vec.0[2] == 131042u32;
     have b_vec.0[3] == 196563u32;
     // Read-only array iteration sums all four original lanes in order.
     mark before_sum_a;
     have at(before_sum_a, a) == 1u32;
     have at(before_sum_a, a_vec.0[0]) == 0u32;
     have at(before_sum_a, a_vec.0[1]) == 0u32;
     have at(before_sum_a, a_vec.0[2]) == 0u32;
     have at(before_sum_a, a_vec.0[3]) == 0u32;
     execute_until(loop(4));
     have a == at(before_sum_a, a) + at(before_sum_a, a_vec.0[0]) + at(before_sum_a, a_vec.0[1]) + at(before_sum_a, a_vec.0[2]) + at(before_sum_a, a_vec.0[3]);
     have a == 1u32 by {
     rewrite(a == at(before_sum_a, a) + at(before_sum_a, a_vec.0[0]) + at(before_sum_a, a_vec.0[1]) + at(before_sum_a, a_vec.0[2]) + at(before_sum_a, a_vec.0[3]));
     rewrite(at(before_sum_a, a) == 1u32);
     rewrite(at(before_sum_a, a_vec.0[0]) == 0u32);
     rewrite(at(before_sum_a, a_vec.0[1]) == 0u32);
     rewrite(at(before_sum_a, a_vec.0[2]) == 0u32);
     rewrite(at(before_sum_a, a_vec.0[3]) == 0u32);
     simp();
     }
     mark before_sum_b;
     have at(before_sum_b, b) == 0u32;
     have at(before_sum_b, b_vec.0[0]) == 0u32;
     have at(before_sum_b, b_vec.0[1]) == 65521u32;
     have at(before_sum_b, b_vec.0[2]) == 131042u32;
     have at(before_sum_b, b_vec.0[3]) == 196563u32;
     execute_until(loop(5));
     have b == at(before_sum_b, b) + at(before_sum_b, b_vec.0[0]) + at(before_sum_b, b_vec.0[1]) + at(before_sum_b, b_vec.0[2]) + at(before_sum_b, b_vec.0[3]);
     have b == 393126u32 by {
     rewrite(b == at(before_sum_b, b) + at(before_sum_b, b_vec.0[0]) + at(before_sum_b, b_vec.0[1]) + at(before_sum_b, b_vec.0[2]) + at(before_sum_b, b_vec.0[3]));
     rewrite(at(before_sum_b, b) == 0u32);
     rewrite(at(before_sum_b, b_vec.0[0]) == 0u32);
     rewrite(at(before_sum_b, b_vec.0[1]) == 65521u32);
     rewrite(at(before_sum_b, b_vec.0[2]) == 131042u32);
     rewrite(at(before_sum_b, b_vec.0[3]) == 196563u32);
     simp();
     }
     // Reduce before narrowing to u16; retain only these checked values in
     // the final store closers.
     execute_until(assignment(__rust_mir_149, 0));
     mark output_a;
     have at(output_a, __rust_mir_150) == 1u32;
     step();
     have at(output_a, __rust_checked_32) == 1u32;
     have at(output_a, __rust_checked_34) == 65521u32;
     have __rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34);
     have __rust_mir_149 == 1u32 by {
     rewrite(__rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34));
     rewrite(at(output_a, __rust_checked_32) == 1u32);
     rewrite(at(output_a, __rust_checked_34) == 65521u32);
     simp();
     }
     mark reduced_a;
     have at(reduced_a, __rust_mir_149) == 1u32;
     execute_until(assignment(__rust_mir_151, 0));
     mark output_b;
     have at(output_b, __rust_mir_152) == 393126u32;
     step();
     have at(output_b, __rust_checked_35) == 393126u32;
     have at(output_b, __rust_checked_37) == 65521u32;
     have __rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37);
     have __rust_mir_151 == 0u32 by {
     rewrite(__rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37));
     rewrite(at(output_b, __rust_checked_35) == 393126u32);
     rewrite(at(output_b, __rust_checked_37) == 65521u32);
     simp();
     }
     mark reduced_b;
     have at(reduced_b, __rust_mir_151) == 0u32;
     execute();
     have self.a == 1 by simp() using { at(reduced_a, __rust_mir_149) == 1u32; };
     have self.b == 0 by simp() using { at(reduced_b, __rust_mir_151) == 0u32; };
     simp() using { self.a == 1; self.b == 0; }
    }
}

// Imported scalar constants
impl adler2::Adler32 {
    fn compute::MOD() -> u32 { ensures result == 65521u32; } by { execute(); simp(); }
}
impl adler2::Adler32 {
    fn compute::CHUNK_SIZE() -> usize { ensures result == 22208u64; } by { execute(); simp(); }
}
