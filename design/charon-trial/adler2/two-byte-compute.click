// Serial-tail boundary of the original, locked Adler32::compute body.
// The fixture harness combines this contract with the helper/getter contracts
// from helpers.click, checks all their bodies, and rechecks the proof tools.
impl adler2::Adler32 {
    fn compute(&mut self, bytes: &[u8]) {
     requires bytes.len() == 2u64;
     requires self.a == 1;
     requires self.b == 0;
     owns self.a;
     owns self.b;
     views bytes[0..2];
     ensures to_integer(self.a) == to_integer((((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)))) % 65521u32);
     ensures bytes[0] == old(bytes[0]);
     ensures bytes[1] == old(bytes[1]);
     ensures to_integer(self.b) == to_integer((((393126u32 + (1u32 + old((bytes[0] as u32)))) + ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))))) % 65521u32);
     ensures to_integer(self.a) == old(adler_spec_a(bytes, 2, 1));
     ensures to_integer(self.b) == old(adler_spec_b(bytes, 2, 1, 0));
    } by {
     apply(adler_serial_two_result_spec(bytes));
     have old(bytes.len()) == 2u64;
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
     // Tail byte 0: the stored cursor/remaining pair advances once.
     execute_until(assignment(__rust_mir_144, 0));
     have remainder == old(bytes);
     have __rust_mir_138_cursor == old(bytes) + 1 by simp() using { remainder == old(bytes); };
     have __rust_mir_138_remaining == 1 by simp() using { old(bytes.len()) == 2u64; };
     have byte == old(bytes[0]) by simp() using { remainder == old(bytes); __rust_mir_138_cursor == old(bytes) + 1; };
     step();
     have __rust_mir_144 <= 255u32;
     apply(uint32_less_equal_to_integer(__rust_mir_144, 255u32));
     have to_integer(a) == 1 by simp() using { a == 1u32; };
     have to_integer(a) <= 1 by arithmetic() using { to_integer(a) == 1; };
     have to_integer(b) == 393126 by simp() using { b == 393126u32; };
     have to_integer(b) <= 393126 by arithmetic() using { to_integer(b) == 393126; };
     have to_integer(a) + to_integer(__rust_mir_144) <= 4294967295 by arithmetic() using { to_integer(a) <= 1; to_integer(__rust_mir_144) <= 255; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_144)) using { to_integer(a) + to_integer(__rust_mir_144) <= 4294967295; }
     execute_until(assignment(__rust_mir_146, 0));
     mark tail_a_1;
     have at(tail_a_1, a) == 1u32;
     have at(tail_a_1, __rust_mir_144) == old((bytes[0] as u32)) by simp() using { byte == old(bytes[0]); };
     have to_integer(at(tail_a_1, a)) <= 1 by simp() using { to_integer(a) <= 1; };
     have to_integer(at(tail_a_1, __rust_mir_144)) <= 255 by simp() using { to_integer(__rust_mir_144) <= 255; };
     have to_integer(at(tail_a_1, a)) + to_integer(at(tail_a_1, __rust_mir_144)) <= 4294967295 by arithmetic() using { to_integer(at(tail_a_1, a)) <= 1; to_integer(at(tail_a_1, __rust_mir_144)) <= 255; };
     step();
     have __rust_mir_146 == at(tail_a_1, a) + at(tail_a_1, __rust_mir_144);
     have __rust_mir_146 == (1u32 + old((bytes[0] as u32))) by {
     rewrite(__rust_mir_146 == at(tail_a_1, a) + at(tail_a_1, __rust_mir_144));
     rewrite(at(tail_a_1, a) == 1u32);
     rewrite(at(tail_a_1, __rust_mir_144) == old((bytes[0] as u32))); simp() using {};
     }
     execute_until(assignment(__rust_mir_147, 0));
     have a == at(tail_a_1, a) + at(tail_a_1, __rust_mir_144) by simp() using { __rust_mir_146 == at(tail_a_1, a) + at(tail_a_1, __rust_mir_144); };
     apply(uint32_add_to_integer(at(tail_a_1, a), at(tail_a_1, __rust_mir_144))) using { to_integer(at(tail_a_1, a)) + to_integer(at(tail_a_1, __rust_mir_144)) <= 4294967295; }
     have to_integer(a) == to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)) by simp() using { a == at(tail_a_1, a) + at(tail_a_1, __rust_mir_144); };
     have to_integer(a) <= 256 by { arithmetic_certificate {
     premise 0: to_integer(a) == to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)) => to_integer(a) == to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144));
     premise 1: to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)) == to_integer(at(tail_a_1, a)) + to_integer(at(tail_a_1, __rust_mir_144)) => to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)) == to_integer(at(tail_a_1, a)) + to_integer(at(tail_a_1, __rust_mir_144));
     add 0, 1 => to_integer(a) + to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)) == to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)) + (to_integer(at(tail_a_1, a)) + to_integer(at(tail_a_1, __rust_mir_144)));
     less_equal_from_equal 2 => to_integer(a) + to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)) <= to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)) + (to_integer(at(tail_a_1, a)) + to_integer(at(tail_a_1, __rust_mir_144)));
     premise 2: to_integer(at(tail_a_1, a)) <= 1 => to_integer(at(tail_a_1, a)) <= 1;
     add 4, 3 => to_integer(at(tail_a_1, a)) + (to_integer(a) + to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144))) <= 1 + (to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)) + (to_integer(at(tail_a_1, a)) + to_integer(at(tail_a_1, __rust_mir_144))));
     premise 3: to_integer(at(tail_a_1, __rust_mir_144)) <= 255 => to_integer(at(tail_a_1, __rust_mir_144)) <= 255;
     add 6, 5 => to_integer(at(tail_a_1, __rust_mir_144)) + (to_integer(at(tail_a_1, a)) + (to_integer(a) + to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)))) <= 255 + (1 + (to_integer(at(tail_a_1, a) + at(tail_a_1, __rust_mir_144)) + (to_integer(at(tail_a_1, a)) + to_integer(at(tail_a_1, __rust_mir_144)))));
     conclusion 7;
     } }
     have to_integer(b) + to_integer(a) <= 4294967295 by arithmetic() using { to_integer(b) <= 393126; to_integer(a) <= 256; };
     apply(uint32_widened_add_guard_by_integer_bound(b, a)) using { to_integer(b) + to_integer(a) <= 4294967295; }
     execute_until(assignment(__rust_mir_148, 0));
     mark tail_b_1;
     have at(tail_b_1, b) == 393126u32;
     have at(tail_b_1, a) == (1u32 + old((bytes[0] as u32)));
     have to_integer(at(tail_b_1, b)) <= 393126 by simp() using { to_integer(b) <= 393126; };
     have to_integer(at(tail_b_1, a)) <= 256 by simp() using { to_integer(a) <= 256; };
     have to_integer(at(tail_b_1, b)) + to_integer(at(tail_b_1, a)) <= 4294967295 by arithmetic() using { to_integer(at(tail_b_1, b)) <= 393126; to_integer(at(tail_b_1, a)) <= 256; };
     step();
     have __rust_mir_148 == at(tail_b_1, b) + at(tail_b_1, a);
     have __rust_mir_148 == (393126u32 + (1u32 + old((bytes[0] as u32)))) by {
     rewrite(__rust_mir_148 == at(tail_b_1, b) + at(tail_b_1, a));
     rewrite(at(tail_b_1, b) == 393126u32);
     rewrite(at(tail_b_1, a) == (1u32 + old((bytes[0] as u32)))); simp() using {};
     }
     apply(uint32_add_to_integer(at(tail_b_1, b), at(tail_b_1, a))) using { to_integer(at(tail_b_1, b)) + to_integer(at(tail_b_1, a)) <= 4294967295; }
     have to_integer(__rust_mir_148) == to_integer(at(tail_b_1, b) + at(tail_b_1, a)) by simp() using { __rust_mir_148 == at(tail_b_1, b) + at(tail_b_1, a); };
     have to_integer(__rust_mir_148) <= 393382 by { arithmetic_certificate {
     premise 0: to_integer(__rust_mir_148) == to_integer(at(tail_b_1, b) + at(tail_b_1, a)) => to_integer(__rust_mir_148) == to_integer(at(tail_b_1, b) + at(tail_b_1, a));
     premise 1: to_integer(at(tail_b_1, b) + at(tail_b_1, a)) == to_integer(at(tail_b_1, b)) + to_integer(at(tail_b_1, a)) => to_integer(at(tail_b_1, b) + at(tail_b_1, a)) == to_integer(at(tail_b_1, b)) + to_integer(at(tail_b_1, a));
     add 0, 1 => to_integer(__rust_mir_148) + to_integer(at(tail_b_1, b) + at(tail_b_1, a)) == to_integer(at(tail_b_1, b) + at(tail_b_1, a)) + (to_integer(at(tail_b_1, b)) + to_integer(at(tail_b_1, a)));
     less_equal_from_equal 2 => to_integer(__rust_mir_148) + to_integer(at(tail_b_1, b) + at(tail_b_1, a)) <= to_integer(at(tail_b_1, b) + at(tail_b_1, a)) + (to_integer(at(tail_b_1, b)) + to_integer(at(tail_b_1, a)));
     premise 2: to_integer(at(tail_b_1, b)) <= 393126 => to_integer(at(tail_b_1, b)) <= 393126;
     add 4, 3 => to_integer(at(tail_b_1, b)) + (to_integer(__rust_mir_148) + to_integer(at(tail_b_1, b) + at(tail_b_1, a))) <= 393126 + (to_integer(at(tail_b_1, b) + at(tail_b_1, a)) + (to_integer(at(tail_b_1, b)) + to_integer(at(tail_b_1, a))));
     premise 3: to_integer(at(tail_b_1, a)) <= 256 => to_integer(at(tail_b_1, a)) <= 256;
     add 6, 5 => to_integer(at(tail_b_1, a)) + (to_integer(at(tail_b_1, b)) + (to_integer(__rust_mir_148) + to_integer(at(tail_b_1, b) + at(tail_b_1, a)))) <= 256 + (393126 + (to_integer(at(tail_b_1, b) + at(tail_b_1, a)) + (to_integer(at(tail_b_1, b)) + to_integer(at(tail_b_1, a)))));
     conclusion 7;
     } }
     // Finish the original store and storage-end nodes, then reach the next loop head.
     step(); step(); step(); step(); step(); step(); step(); step(); step(); step();
     // Tail byte 1: the stored cursor/remaining pair advances once.
     execute_until(assignment(__rust_mir_144, 0));
     have remainder == old(bytes);
     have __rust_mir_138_cursor == old(bytes) + 2 by simp() using { remainder == old(bytes); };
     have __rust_mir_138_remaining == 0 by simp() using { old(bytes.len()) == 2u64; };
     have byte == old(bytes[1]) by simp() using { remainder == old(bytes); __rust_mir_138_cursor == old(bytes) + 2; };
     step();
     have __rust_mir_144 <= 255u32;
     apply(uint32_less_equal_to_integer(__rust_mir_144, 255u32));
     have to_integer(b) <= 393382 by simp() using { to_integer(__rust_mir_148) <= 393382; };
     have to_integer(a) + to_integer(__rust_mir_144) <= 4294967295 by arithmetic() using { to_integer(a) <= 256; to_integer(__rust_mir_144) <= 255; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_144)) using { to_integer(a) + to_integer(__rust_mir_144) <= 4294967295; }
     execute_until(assignment(__rust_mir_146, 0));
     mark tail_a_2;
     have at(tail_a_2, a) == (1u32 + old((bytes[0] as u32)));
     have at(tail_a_2, __rust_mir_144) == old((bytes[1] as u32)) by simp() using { byte == old(bytes[1]); };
     have to_integer(at(tail_a_2, a)) <= 256 by simp() using { to_integer(a) <= 256; };
     have to_integer(at(tail_a_2, __rust_mir_144)) <= 255 by simp() using { to_integer(__rust_mir_144) <= 255; };
     have to_integer(at(tail_a_2, a)) + to_integer(at(tail_a_2, __rust_mir_144)) <= 4294967295 by arithmetic() using { to_integer(at(tail_a_2, a)) <= 256; to_integer(at(tail_a_2, __rust_mir_144)) <= 255; };
     step();
     have __rust_mir_146 == at(tail_a_2, a) + at(tail_a_2, __rust_mir_144);
     have __rust_mir_146 == ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))) by {
     rewrite(__rust_mir_146 == at(tail_a_2, a) + at(tail_a_2, __rust_mir_144));
     rewrite(at(tail_a_2, a) == (1u32 + old((bytes[0] as u32))));
     rewrite(at(tail_a_2, __rust_mir_144) == old((bytes[1] as u32))); simp() using {};
     }
     execute_until(assignment(__rust_mir_147, 0));
     have a == at(tail_a_2, a) + at(tail_a_2, __rust_mir_144) by simp() using { __rust_mir_146 == at(tail_a_2, a) + at(tail_a_2, __rust_mir_144); };
     apply(uint32_add_to_integer(at(tail_a_2, a), at(tail_a_2, __rust_mir_144))) using { to_integer(at(tail_a_2, a)) + to_integer(at(tail_a_2, __rust_mir_144)) <= 4294967295; }
     have to_integer(a) == to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)) by simp() using { a == at(tail_a_2, a) + at(tail_a_2, __rust_mir_144); };
     have to_integer(a) <= 511 by { arithmetic_certificate {
     premise 0: to_integer(a) == to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)) => to_integer(a) == to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144));
     premise 1: to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)) == to_integer(at(tail_a_2, a)) + to_integer(at(tail_a_2, __rust_mir_144)) => to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)) == to_integer(at(tail_a_2, a)) + to_integer(at(tail_a_2, __rust_mir_144));
     add 0, 1 => to_integer(a) + to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)) == to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)) + (to_integer(at(tail_a_2, a)) + to_integer(at(tail_a_2, __rust_mir_144)));
     less_equal_from_equal 2 => to_integer(a) + to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)) <= to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)) + (to_integer(at(tail_a_2, a)) + to_integer(at(tail_a_2, __rust_mir_144)));
     premise 2: to_integer(at(tail_a_2, a)) <= 256 => to_integer(at(tail_a_2, a)) <= 256;
     add 4, 3 => to_integer(at(tail_a_2, a)) + (to_integer(a) + to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144))) <= 256 + (to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)) + (to_integer(at(tail_a_2, a)) + to_integer(at(tail_a_2, __rust_mir_144))));
     premise 3: to_integer(at(tail_a_2, __rust_mir_144)) <= 255 => to_integer(at(tail_a_2, __rust_mir_144)) <= 255;
     add 6, 5 => to_integer(at(tail_a_2, __rust_mir_144)) + (to_integer(at(tail_a_2, a)) + (to_integer(a) + to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)))) <= 255 + (256 + (to_integer(at(tail_a_2, a) + at(tail_a_2, __rust_mir_144)) + (to_integer(at(tail_a_2, a)) + to_integer(at(tail_a_2, __rust_mir_144)))));
     conclusion 7;
     } }
     have to_integer(b) + to_integer(a) <= 4294967295 by arithmetic() using { to_integer(b) <= 393382; to_integer(a) <= 511; };
     apply(uint32_widened_add_guard_by_integer_bound(b, a)) using { to_integer(b) + to_integer(a) <= 4294967295; }
     execute_until(assignment(__rust_mir_148, 0));
     mark tail_b_2;
     have at(tail_b_2, b) == (393126u32 + (1u32 + old((bytes[0] as u32))));
     have at(tail_b_2, a) == ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)));
     have to_integer(at(tail_b_2, b)) <= 393382 by simp() using { to_integer(b) <= 393382; };
     have to_integer(at(tail_b_2, a)) <= 511 by simp() using { to_integer(a) <= 511; };
     have to_integer(at(tail_b_2, b)) + to_integer(at(tail_b_2, a)) <= 4294967295 by arithmetic() using { to_integer(at(tail_b_2, b)) <= 393382; to_integer(at(tail_b_2, a)) <= 511; };
     step();
     have __rust_mir_148 == at(tail_b_2, b) + at(tail_b_2, a);
     have __rust_mir_148 == ((393126u32 + (1u32 + old((bytes[0] as u32)))) + ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)))) by {
     rewrite(__rust_mir_148 == at(tail_b_2, b) + at(tail_b_2, a));
     rewrite(at(tail_b_2, b) == (393126u32 + (1u32 + old((bytes[0] as u32)))));
     rewrite(at(tail_b_2, a) == ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)))); simp() using {};
     }
     apply(uint32_add_to_integer(at(tail_b_2, b), at(tail_b_2, a))) using { to_integer(at(tail_b_2, b)) + to_integer(at(tail_b_2, a)) <= 4294967295; }
     have to_integer(__rust_mir_148) == to_integer(at(tail_b_2, b) + at(tail_b_2, a)) by simp() using { __rust_mir_148 == at(tail_b_2, b) + at(tail_b_2, a); };
     have to_integer(__rust_mir_148) <= 393893 by { arithmetic_certificate {
     premise 0: to_integer(__rust_mir_148) == to_integer(at(tail_b_2, b) + at(tail_b_2, a)) => to_integer(__rust_mir_148) == to_integer(at(tail_b_2, b) + at(tail_b_2, a));
     premise 1: to_integer(at(tail_b_2, b) + at(tail_b_2, a)) == to_integer(at(tail_b_2, b)) + to_integer(at(tail_b_2, a)) => to_integer(at(tail_b_2, b) + at(tail_b_2, a)) == to_integer(at(tail_b_2, b)) + to_integer(at(tail_b_2, a));
     add 0, 1 => to_integer(__rust_mir_148) + to_integer(at(tail_b_2, b) + at(tail_b_2, a)) == to_integer(at(tail_b_2, b) + at(tail_b_2, a)) + (to_integer(at(tail_b_2, b)) + to_integer(at(tail_b_2, a)));
     less_equal_from_equal 2 => to_integer(__rust_mir_148) + to_integer(at(tail_b_2, b) + at(tail_b_2, a)) <= to_integer(at(tail_b_2, b) + at(tail_b_2, a)) + (to_integer(at(tail_b_2, b)) + to_integer(at(tail_b_2, a)));
     premise 2: to_integer(at(tail_b_2, b)) <= 393382 => to_integer(at(tail_b_2, b)) <= 393382;
     add 4, 3 => to_integer(at(tail_b_2, b)) + (to_integer(__rust_mir_148) + to_integer(at(tail_b_2, b) + at(tail_b_2, a))) <= 393382 + (to_integer(at(tail_b_2, b) + at(tail_b_2, a)) + (to_integer(at(tail_b_2, b)) + to_integer(at(tail_b_2, a))));
     premise 3: to_integer(at(tail_b_2, a)) <= 511 => to_integer(at(tail_b_2, a)) <= 511;
     add 6, 5 => to_integer(at(tail_b_2, a)) + (to_integer(at(tail_b_2, b)) + (to_integer(__rust_mir_148) + to_integer(at(tail_b_2, b) + at(tail_b_2, a)))) <= 511 + (393382 + (to_integer(at(tail_b_2, b) + at(tail_b_2, a)) + (to_integer(at(tail_b_2, b)) + to_integer(at(tail_b_2, a)))));
     conclusion 7;
     } }
     execute_until(assignment(__rust_mir_149, 0));
     mark output_a;
     step();
     have at(output_a, __rust_checked_32) == ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)));
     have at(output_a, __rust_checked_34) == 65521u32;
     have __rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34);
     have __rust_mir_149 == (((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)))) % 65521u32 by {
     rewrite(__rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34));
     rewrite(at(output_a, __rust_checked_32) == ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))));
     rewrite(at(output_a, __rust_checked_34) == 65521u32); simp();
     }
     apply(uint32_remainder_less_than_divisor(at(output_a, __rust_checked_32), 65521u32));
     have __rust_mir_149 < 65521u32 by simp() using { __rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34); at(output_a, __rust_checked_34) == 65521u32; at(output_a, __rust_checked_32) % 65521u32 < 65521u32; };
     apply(uint32_to_integer_bounds(__rust_mir_149));
     apply(uint32_less_than_to_integer(__rust_mir_149, 65521u32));
     have to_integer(__rust_mir_149) <= 65535 by arithmetic() using { to_integer(__rust_mir_149) < 65521; };
     mark reduced_a;
     execute_until(assignment(__rust_mir_151, 0));
     mark output_b;
     step();
     have at(output_b, __rust_checked_35) == ((393126u32 + (1u32 + old((bytes[0] as u32)))) + ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))));
     have at(output_b, __rust_checked_37) == 65521u32;
     have __rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37);
     have __rust_mir_151 == (((393126u32 + (1u32 + old((bytes[0] as u32)))) + ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))))) % 65521u32 by {
     rewrite(__rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37));
     rewrite(at(output_b, __rust_checked_35) == ((393126u32 + (1u32 + old((bytes[0] as u32)))) + ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)))));
     rewrite(at(output_b, __rust_checked_37) == 65521u32); simp();
     }
     apply(uint32_remainder_less_than_divisor(at(output_b, __rust_checked_35), 65521u32));
     have __rust_mir_151 < 65521u32 by simp() using { __rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37); at(output_b, __rust_checked_37) == 65521u32; at(output_b, __rust_checked_35) % 65521u32 < 65521u32; };
     apply(uint32_to_integer_bounds(__rust_mir_151));
     apply(uint32_less_than_to_integer(__rust_mir_151, 65521u32));
     have to_integer(__rust_mir_151) <= 65535 by arithmetic() using { to_integer(__rust_mir_151) < 65521; };
     mark reduced_b;
     execute();
     have to_integer(self.a) == to_integer(at(reduced_a, __rust_mir_149)) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer(at(reduced_a, __rust_mir_149)) => 0 <= to_integer(at(reduced_a, __rust_mir_149));
     premise 1: to_integer(at(reduced_a, __rust_mir_149)) <= 65535 => to_integer(at(reduced_a, __rust_mir_149)) <= 65535;
     integer_cast_identity bounds [0, 1] => to_integer(self.a) == to_integer(at(reduced_a, __rust_mir_149)); conclusion 0;
     } }
     have to_integer(self.b) == to_integer(at(reduced_b, __rust_mir_151)) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer(at(reduced_b, __rust_mir_151)) => 0 <= to_integer(at(reduced_b, __rust_mir_151));
     premise 1: to_integer(at(reduced_b, __rust_mir_151)) <= 65535 => to_integer(at(reduced_b, __rust_mir_151)) <= 65535;
     integer_cast_identity bounds [0, 1] => to_integer(self.b) == to_integer(at(reduced_b, __rust_mir_151)); conclusion 0;
     } }
     have bytes[0] == old(bytes[0]) by simp() using {};
     have bytes[1] == old(bytes[1]) by simp() using {};
     have to_integer(self.a) == to_integer((((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)))) % 65521u32) by {
      rewrite(to_integer(self.a) == to_integer(at(reduced_a, __rust_mir_149)));
      rewrite(at(reduced_a, __rust_mir_149) == (((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)))) % 65521u32); normalize();
     }
     have to_integer((((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)))) % 65521u32) == old(adler_spec_a(bytes, 2, 1)) by assumption();
     have to_integer(self.a) == old(adler_spec_a(bytes, 2, 1)) by {
      rewrite(to_integer(self.a) == to_integer((((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)))) % 65521u32)); assumption();
     }
     have to_integer(self.b) == to_integer((((393126u32 + (1u32 + old((bytes[0] as u32)))) + ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))))) % 65521u32) by {
      rewrite(to_integer(self.b) == to_integer(at(reduced_b, __rust_mir_151)));
      rewrite(at(reduced_b, __rust_mir_151) == (((393126u32 + (1u32 + old((bytes[0] as u32)))) + ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))))) % 65521u32); normalize();
     }
     have to_integer((((393126u32 + (1u32 + old((bytes[0] as u32)))) + ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))))) % 65521u32) == old(adler_spec_b(bytes, 2, 1, 0)) by assumption();
     have to_integer(self.b) == old(adler_spec_b(bytes, 2, 1, 0)) by {
      rewrite(to_integer(self.b) == to_integer((((393126u32 + (1u32 + old((bytes[0] as u32)))) + ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))))) % 65521u32)); assumption();
     }
     simp() using { to_integer(self.a) == old(adler_spec_a(bytes, 2, 1)); to_integer(self.b) == old(adler_spec_b(bytes, 2, 1, 0)); bytes[0] == old(bytes[0]); bytes[1] == old(bytes[1]); to_integer(self.a) == to_integer(at(reduced_a, __rust_mir_149)); at(reduced_a, __rust_mir_149) == (((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32)))) % 65521u32; to_integer(self.b) == to_integer(at(reduced_b, __rust_mir_151)); at(reduced_b, __rust_mir_151) == (((393126u32 + (1u32 + old((bytes[0] as u32)))) + ((1u32 + old((bytes[0] as u32))) + old((bytes[1] as u32))))) % 65521u32; }
    }
}
