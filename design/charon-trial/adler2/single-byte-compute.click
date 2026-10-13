// Single-byte boundary of the original, locked Adler32::compute body.
// The fixture harness combines this contract with the helper/getter contracts
// from helpers.click, checks all their bodies, and rechecks the proof tools.
impl adler2::Adler32 {
    fn compute(&mut self, bytes: &[u8]) {
     requires bytes.len() == 1u64;
     requires self.a == 1;
     requires self.b == 0;
     owns self.a;
     owns self.b;
     views bytes[0..1];
     ensures to_integer(self.a) == to_integer((1u32 + old((bytes[0] as u32))) % 65521u32);
     ensures bytes[0] == old(bytes[0]);
     ensures to_integer(self.b) == to_integer((393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32);
     ensures to_integer(self.a) == old(adler_spec_a(bytes, 1, 1));
     ensures to_integer(self.b) == old(adler_spec_b(bytes, 1, 1, 0));
    } by {

     apply(adler_spec_one(bytes));
     apply(adler_byte_bounds(bytes[0]));
     have to_integer((bytes[0] as u32)) == to_integer((bytes[0] as i32)) by { arithmetic_certificate rules {
     premise 0: 0 <= to_integer((bytes[0] as i32)) => 0 <= to_integer((bytes[0] as i32));
     premise 1: to_integer((bytes[0] as i32)) <= 255 => to_integer((bytes[0] as i32)) <= 255;
     integer_cast_identity bounds [0, 1] => to_integer((bytes[0] as u32)) == to_integer((bytes[0] as i32)); conclusion 0;
     } }
     have 0 <= to_integer((bytes[0] as u32)) by arithmetic() using { 0 <= to_integer((bytes[0] as i32)); to_integer((bytes[0] as u32)) == to_integer((bytes[0] as i32)); };
     have to_integer((bytes[0] as u32)) <= 255 by arithmetic() using { to_integer((bytes[0] as i32)) <= 255; to_integer((bytes[0] as u32)) == to_integer((bytes[0] as i32)); };
     have to_integer(1u32) + to_integer((bytes[0] as u32)) <= 4294967295 by arithmetic() using { to_integer((bytes[0] as u32)) <= 255; };
     apply(uint32_add_to_integer(1u32, (bytes[0] as u32)));
     have to_integer(393126u32) + to_integer(1u32 + (bytes[0] as u32)) <= 4294967295 by arithmetic() using { to_integer(1u32 + (bytes[0] as u32)) == to_integer(1u32) + to_integer((bytes[0] as u32)); to_integer((bytes[0] as u32)) <= 255; };
     apply(uint32_add_to_integer(393126u32, 1u32 + (bytes[0] as u32)));
     apply(uint32_remainder_to_integer(1u32 + (bytes[0] as u32), 65521u32));
     apply(uint32_remainder_to_integer(393126u32 + (1u32 + (bytes[0] as u32)), 65521u32));
     have 0 <= 1 + to_integer((bytes[0] as u32)) by arithmetic() using { 0 <= to_integer((bytes[0] as u32)); };
     have 0 <= 393126 + (1 + to_integer((bytes[0] as u32))) by arithmetic() using { 0 <= to_integer((bytes[0] as u32)); };
     have 393126 + (1 + to_integer((bytes[0] as u32))) == (1 + to_integer((bytes[0] as u32))) + 65521 * 6 by arithmetic() using {};
     apply(adler_residue_congruent(393126 + (1 + to_integer((bytes[0] as u32))), 1 + to_integer((bytes[0] as u32)), 6));

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
     execute_until(assignment(__rust_mir_144, 0));
     have remainder == old(bytes);
     have byte == old(bytes[0]) by simp() using { remainder == old(bytes); };
     step();
     have __rust_mir_144 <= 255u32;
     apply(uint32_to_integer_bounds(__rust_mir_144));
     apply(uint32_less_equal_to_integer(__rust_mir_144, 255u32));
     have to_integer(a) == 1 by simp() using { a == 1u32; };
     have to_integer(a) + to_integer(__rust_mir_144) <= 4294967295 by arithmetic() using { to_integer(a) == 1; to_integer(__rust_mir_144) <= 255; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_144)) using { to_integer(a) + to_integer(__rust_mir_144) <= 4294967295; }
     execute_until(assignment(__rust_mir_146, 0));
     mark tail_a;
     have at(tail_a, a) == 1u32 by simp() using { a == 1u32; };
     have at(tail_a, __rust_mir_144) == old((bytes[0] as u32));
     step();
     have __rust_mir_146 == at(tail_a, a) + at(tail_a, __rust_mir_144);
     have __rust_mir_146 == 1u32 + old((bytes[0] as u32)) by {
     rewrite(__rust_mir_146 == at(tail_a, a) + at(tail_a, __rust_mir_144));
     rewrite(at(tail_a, a) == 1u32);
     rewrite(at(tail_a, __rust_mir_144) == old((bytes[0] as u32)));
     simp();
     }
     execute_until(assignment(__rust_mir_147, 0));
     have old((bytes[0] as u32)) <= 255u32 by simp() using { at(tail_a, __rust_mir_144) == old((bytes[0] as u32)); at(tail_a, __rust_mir_144) <= 255u32; };
     apply(uint32_less_equal_to_integer(old((bytes[0] as u32)), 255u32));
     have to_integer(1u32) + to_integer(old((bytes[0] as u32))) <= 4294967295 by arithmetic() using { to_integer(old((bytes[0] as u32))) <= 255; };
     apply(uint32_add_to_integer(1u32, old((bytes[0] as u32)))) using { to_integer(1u32) + to_integer(old((bytes[0] as u32))) <= 4294967295; }
     have to_integer(a) == to_integer(1u32 + old((bytes[0] as u32))) by simp() using { a == 1u32 + old((bytes[0] as u32)); };
     have to_integer(a) <= 256 by {
     arithmetic_certificate {
     premise 0: to_integer(a) == to_integer(1u32 + old((bytes[0] as u32))) => to_integer(a) == to_integer(1u32 + old((bytes[0] as u32)));
     premise 1: to_integer(1u32 + old((bytes[0] as u32))) == to_integer(1u32) + to_integer(old((bytes[0] as u32))) => to_integer(1u32 + old((bytes[0] as u32))) == to_integer(1u32) + to_integer(old((bytes[0] as u32)));
     add 0, 1 => to_integer(a) + to_integer(1u32 + old((bytes[0] as u32))) == to_integer(1u32 + old((bytes[0] as u32))) + (to_integer(1u32) + to_integer(old((bytes[0] as u32))));
     less_equal_from_equal 2 => to_integer(a) + to_integer(1u32 + old((bytes[0] as u32))) <= to_integer(1u32 + old((bytes[0] as u32))) + (to_integer(1u32) + to_integer(old((bytes[0] as u32))));
     premise 2: to_integer(old((bytes[0] as u32))) <= 255 => to_integer(old((bytes[0] as u32))) <= 255;
     add 4, 3 => to_integer(old((bytes[0] as u32))) + (to_integer(a) + to_integer(1u32 + old((bytes[0] as u32)))) <= 255 + (to_integer(1u32 + old((bytes[0] as u32))) + (to_integer(1u32) + to_integer(old((bytes[0] as u32)))));
     conclusion 5;
     }
     }
     have to_integer(b) == 393126 by simp() using { b == 393126u32; };
     have to_integer(b) + to_integer(a) <= 4294967295 by arithmetic() using { to_integer(b) == 393126; to_integer(a) <= 256; };
     apply(uint32_widened_add_guard_by_integer_bound(b, a)) using { to_integer(b) + to_integer(a) <= 4294967295; }
     execute_until(assignment(__rust_mir_148, 0));
     mark tail_b;
     have at(tail_b, b) == 393126u32;
     have at(tail_b, a) == 1u32 + old((bytes[0] as u32));
     step();
     have __rust_mir_148 == at(tail_b, b) + at(tail_b, a);
     have __rust_mir_148 == 393126u32 + (1u32 + old((bytes[0] as u32))) by {
     rewrite(__rust_mir_148 == at(tail_b, b) + at(tail_b, a));
     rewrite(at(tail_b, b) == 393126u32);
     rewrite(at(tail_b, a) == 1u32 + old((bytes[0] as u32)));
     simp();
     }
     execute_until(assignment(__rust_mir_149, 0));
     mark output_a;
     step();
     have at(output_a, __rust_checked_32) == 1u32 + old((bytes[0] as u32));
     have at(output_a, __rust_checked_34) == 65521u32;
     have __rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34);
     have __rust_mir_149 == (1u32 + old((bytes[0] as u32))) % 65521u32 by {
     rewrite(__rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34));
     rewrite(at(output_a, __rust_checked_32) == 1u32 + old((bytes[0] as u32)));
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
     have at(output_b, __rust_checked_35) == 393126u32 + (1u32 + old((bytes[0] as u32)));
     have at(output_b, __rust_checked_37) == 65521u32;
     have __rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37);
     have __rust_mir_151 == (393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32 by {
     rewrite(__rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37));
     rewrite(at(output_b, __rust_checked_35) == 393126u32 + (1u32 + old((bytes[0] as u32))));
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
     have old(adler_spec_a(bytes, 1, 1)) == truncating_remainder(1 + to_integer(old((bytes[0] as i32))), 65521) by assumption();
     have old(adler_spec_b(bytes, 1, 1, 0)) == truncating_remainder(1 + to_integer(old((bytes[0] as i32))), 65521) by assumption();
     have to_integer(self.a) == to_integer((1u32 + old((bytes[0] as u32))) % 65521u32) by {
     rewrite(to_integer(self.a) == to_integer(at(reduced_a, __rust_mir_149)));
     rewrite(at(reduced_a, __rust_mir_149) == (1u32 + old((bytes[0] as u32))) % 65521u32);
     simp();
     }
     have to_integer((1u32 + old((bytes[0] as u32))) % 65521u32) == truncating_remainder(to_integer(1u32 + old((bytes[0] as u32))), 65521) by assumption();
     have to_integer(1u32 + old((bytes[0] as u32))) == 1 + to_integer(old((bytes[0] as u32))) by assumption();
     have to_integer(self.a) == old(adler_spec_a(bytes, 1, 1)) by {
     rewrite(to_integer(self.a) == to_integer((1u32 + old((bytes[0] as u32))) % 65521u32));
     rewrite(to_integer((1u32 + old((bytes[0] as u32))) % 65521u32) == truncating_remainder(to_integer(1u32 + old((bytes[0] as u32))), 65521));
     rewrite(to_integer(1u32 + old((bytes[0] as u32))) == 1 + to_integer(old((bytes[0] as u32))));
     rewrite(old(adler_spec_a(bytes, 1, 1)) == truncating_remainder(1 + to_integer(old((bytes[0] as i32))), 65521));
     rewrite(to_integer(old((bytes[0] as u32))) == to_integer(old((bytes[0] as i32))));
     simp();
     }
     have to_integer(self.b) == to_integer((393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32) by {
     rewrite(to_integer(self.b) == to_integer(at(reduced_b, __rust_mir_151)));
     rewrite(at(reduced_b, __rust_mir_151) == (393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32);
     simp();
     }
     have to_integer((393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32) == truncating_remainder(to_integer(393126u32 + (1u32 + old((bytes[0] as u32)))), 65521) by assumption();
     have to_integer(393126u32 + (1u32 + old((bytes[0] as u32)))) == 393126 + to_integer(1u32 + old((bytes[0] as u32))) by assumption();
     have to_integer(self.b) == old(adler_spec_b(bytes, 1, 1, 0)) by {
     rewrite(to_integer(self.b) == to_integer((393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32));
     rewrite(to_integer((393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32) == truncating_remainder(to_integer(393126u32 + (1u32 + old((bytes[0] as u32)))), 65521));
     rewrite(to_integer(393126u32 + (1u32 + old((bytes[0] as u32)))) == 393126 + to_integer(1u32 + old((bytes[0] as u32))));
     rewrite(to_integer(1u32 + old((bytes[0] as u32))) == 1 + to_integer(old((bytes[0] as u32))));
     rewrite(truncating_remainder(393126 + (1 + to_integer(old((bytes[0] as u32)))), 65521) == truncating_remainder(1 + to_integer(old((bytes[0] as u32))), 65521));
     rewrite(old(adler_spec_b(bytes, 1, 1, 0)) == truncating_remainder(1 + to_integer(old((bytes[0] as i32))), 65521));
     rewrite(to_integer(old((bytes[0] as u32))) == to_integer(old((bytes[0] as i32))));
     simp();
     }

     simp() using { bytes[0] == old(bytes[0]); to_integer(self.a) == to_integer(at(reduced_a, __rust_mir_149)); at(reduced_a, __rust_mir_149) == (1u32 + old((bytes[0] as u32))) % 65521u32; to_integer(self.b) == to_integer(at(reduced_b, __rust_mir_151)); at(reduced_b, __rust_mir_151) == (393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32; to_integer(self.a) == old(adler_spec_a(bytes, 1, 1)); to_integer(self.b) == old(adler_spec_b(bytes, 1, 1, 0)); }
    }
}
