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
     ensures to_integer(self.a) == old(adler_spec_a(bytes.as_ptr(), 1, 1));
     ensures to_integer(self.b) == old(adler_spec_b(bytes.as_ptr(), 1, 1, 0));
    } by {

     apply(adler_spec_one(bytes.as_ptr()));
     apply(adler_byte_bounds(bytes[0]));
     have to_integer((bytes[0] as u32)) == to_integer((bytes[0] as i32)) by { close() using { 0 <= to_integer((bytes[0] as i32)); to_integer((bytes[0] as i32)) <= 255; }; }
     have 0 <= to_integer((bytes[0] as u32)) by close() using { 0 <= to_integer((bytes[0] as i32)); to_integer((bytes[0] as u32)) == to_integer((bytes[0] as i32)); };
     have to_integer((bytes[0] as u32)) <= 255 by close() using { to_integer((bytes[0] as i32)) <= 255; to_integer((bytes[0] as u32)) == to_integer((bytes[0] as i32)); };
     have to_integer(1u32) + to_integer((bytes[0] as u32)) <= 4294967295 by close() using { to_integer((bytes[0] as u32)) <= 255; };
     have to_integer(1u32 + ((bytes[0] as u32))) == to_integer(1u32) + to_integer(((bytes[0] as u32)));
     have to_integer(393126u32) + to_integer(1u32 + (bytes[0] as u32)) <= 4294967295 by close() using { to_integer(1u32 + (bytes[0] as u32)) == to_integer(1u32) + to_integer((bytes[0] as u32)); to_integer((bytes[0] as u32)) <= 255; };
     have 0 <= 1 + to_integer((bytes[0] as u32)) by close() using { 0 <= to_integer((bytes[0] as u32)); };
     have 0 <= 393126 + (1 + to_integer((bytes[0] as u32))) by close() using { 0 <= to_integer((bytes[0] as u32)); };
     have 393126 + (1 + to_integer((bytes[0] as u32))) == (1 + to_integer((bytes[0] as u32))) + 65521 * 6 by close() using {};
     apply(adler_residue_congruent(393126 + (1 + to_integer((bytes[0] as u32))), 1 + to_integer((bytes[0] as u32)), 6));

     // The empty chunk iterators execute no body. Prove the scalar reduction
     // from its checked transition before following lane recombination.
     step_until(assignment(b, 0).entry); step();
     have b == 0u32;
     // Neither chunk iterator has any bytes available to yield.
     step_until(loop(0).entry);
     have loop(0).iter.v.len() == 0u64;
     have remainder_chunk.len() == 0u64;
     step_until(loop(2).entry);
     have loop(2).iter.v.len() == 0u64;
     step_until(assignment(b, 3).entry);
     have b == 0u32;
     have remainder_chunk.len() == 0u64;
     step();
     have b == 0u32;
     step_until(assignment(b, 4).entry);
     mark scalar_mod;
     have at(scalar_mod, b) == 0u32;
     step();
     have b == at(scalar_mod, b) % 65521u32;
     have b == 0u32 by {
     rewrite(b, at(scalar_mod, b) % 65521u32);
     rewrite(at(scalar_mod, b), 0u32);
     close();
     }
     // Both lane vectors are still zero: neither loop ran, and each reduction
     // and the multiplication by four keep a zero lane zero.
     have a_vec.0[0] == 0u32;
     have a_vec.0[1] == 0u32;
     have a_vec.0[2] == 0u32;
     have a_vec.0[3] == 0u32;
     have b_vec.0[0] == 0u32;
     have b_vec.0[1] == 0u32;
     have b_vec.0[2] == 0u32;
     have b_vec.0[3] == 0u32;
     have b_vec.0[0] <= 1073741823u32 by close() using { b_vec.0[0] == 0u32; };
     have b_vec.0[1] <= 1073741823u32 by close() using { b_vec.0[1] == 0u32; };
     have b_vec.0[2] <= 1073741823u32 by close() using { b_vec.0[2] == 0u32; };
     have b_vec.0[3] <= 1073741823u32 by close() using { b_vec.0[3] == 0u32; };
     // The three corrections add MOD, twice MOD, and three times MOD.
     step_until(statement(16).entry);
     have b_vec.0[0] == 0u32;
     have b_vec.0[1] == 0u32;
     have b_vec.0[2] == 0u32;
     have b_vec.0[3] == 0u32;
     step_until(statement(17).entry);
     have b_vec.0[1] == 65521u32;
     step_until(statement(18).entry);
     have b_vec.0[2] == 131042u32;
     step_until(loop(3).entry);
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
     step_until(loop(4).entry);
     have a == at(before_sum_a, a) + at(before_sum_a, a_vec.0[0]) + at(before_sum_a, a_vec.0[1]) + at(before_sum_a, a_vec.0[2]) + at(before_sum_a, a_vec.0[3]);
     have a == 1u32 by {
     rewrite(a, at(before_sum_a, a) + at(before_sum_a, a_vec.0[0]) + at(before_sum_a, a_vec.0[1]) + at(before_sum_a, a_vec.0[2]) + at(before_sum_a, a_vec.0[3]));
     rewrite(at(before_sum_a, a), 1u32);
     rewrite(at(before_sum_a, a_vec.0[0]), 0u32);
     rewrite(at(before_sum_a, a_vec.0[1]), 0u32);
     rewrite(at(before_sum_a, a_vec.0[2]), 0u32);
     rewrite(at(before_sum_a, a_vec.0[3]), 0u32);
     close();
     }
     mark before_sum_b;
     have at(before_sum_b, b) == 0u32;
     have at(before_sum_b, b_vec.0[0]) == 0u32;
     have at(before_sum_b, b_vec.0[1]) == 65521u32;
     have at(before_sum_b, b_vec.0[2]) == 131042u32;
     have at(before_sum_b, b_vec.0[3]) == 196563u32;
     step_until(loop(5).entry);
     have b == at(before_sum_b, b) + at(before_sum_b, b_vec.0[0]) + at(before_sum_b, b_vec.0[1]) + at(before_sum_b, b_vec.0[2]) + at(before_sum_b, b_vec.0[3]) by {
     rewrite(at(before_sum_b, b), 0u32);
     rewrite(at(before_sum_b, b_vec.0[0]), 0u32);
     rewrite(at(before_sum_b, b_vec.0[1]), 65521u32);
     rewrite(at(before_sum_b, b_vec.0[2]), 131042u32);
     rewrite(at(before_sum_b, b_vec.0[3]), 196563u32);
     close();
     }
     have b == 393126u32 by {
     rewrite(b, at(before_sum_b, b) + at(before_sum_b, b_vec.0[0]) + at(before_sum_b, b_vec.0[1]) + at(before_sum_b, b_vec.0[2]) + at(before_sum_b, b_vec.0[3]));
     rewrite(at(before_sum_b, b), 0u32);
     rewrite(at(before_sum_b, b_vec.0[0]), 0u32);
     rewrite(at(before_sum_b, b_vec.0[1]), 65521u32);
     rewrite(at(before_sum_b, b_vec.0[2]), 131042u32);
     rewrite(at(before_sum_b, b_vec.0[3]), 196563u32);
     close();
     }
     // Follow each serial iteration at its two accumulator updates.
     have loop(5).iter.len() == 1u64;
     have loop(5).iter.as_slice().as_ptr() == old(bytes.as_ptr()) + 0u64;
     step_until(loop(5).statement(0).entry);
     have byte == old(bytes[0]) by { close(); }
     have a == 1u32;
     have to_integer(a) <= 1;
     have to_integer(byte as u32) <= 255;
     have to_integer(a) + to_integer(byte as u32) <= 4294967295 by {
      close() using { to_integer(a) <= 1; to_integer(byte as u32) <= 255; };
     }
     have a <= 4294967295u32 - (byte as u32);
     mark tail_0_a;
     apply(integer::uint32_add_to_integer(at(tail_0_a, a), at(tail_0_a, byte as u32)));
     step_until(loop(5).statement(1).entry);
     have a == at(tail_0_a, a) + at(tail_0_a, byte as u32);
     have a == (1u32 + old((bytes[0] as u32)));
     have to_integer(a) <= 256;
     have b == 393126u32;
     have to_integer(b) <= 393126;
     have to_integer(b) + to_integer(a) <= 4294967295 by {
      close() using { to_integer(b) <= 393126; to_integer(a) <= 256; };
     }
     have b <= 4294967295u32 - a;
     mark tail_0_b;
     apply(integer::uint32_add_to_integer(at(tail_0_b, b), at(tail_0_b, a)));
     step_until(assignment(b, 6).entry); step();
     have b == at(tail_0_b, b) + at(tail_0_b, a);
     have b == (393126u32 + (1u32 + old((bytes[0] as u32))));
     step_until(statement(22).entry);
     mark output_a;
     have at(output_a, a) == 1u32 + old((bytes[0] as u32));
     have (at(output_a, a) % 65521u32) == (1u32 + old((bytes[0] as u32))) % 65521u32 by {
     rewrite(at(output_a, a), 1u32 + old((bytes[0] as u32)));
     close();
     }
     have (at(output_a, a)) % 65521u32 < 65521u32;
     have 0 <= to_integer((at(output_a, a) % 65521u32));
     have to_integer((at(output_a, a) % 65521u32)) <= 4294967295;
     have to_integer((at(output_a, a) % 65521u32)) < to_integer(65521u32);
     have to_integer((at(output_a, a) % 65521u32)) <= 65535 by close() using { to_integer((at(output_a, a) % 65521u32)) < 65521; };
     step_until(statement(23).entry);
     mark output_b;
     have at(output_b, b) == 393126u32 + (1u32 + old((bytes[0] as u32)));
     have (at(output_b, b) % 65521u32) == (393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32 by {
     rewrite(at(output_b, b), 393126u32 + (1u32 + old((bytes[0] as u32))));
     close();
     }
     have (at(output_b, b)) % 65521u32 < 65521u32;
     have 0 <= to_integer((at(output_b, b) % 65521u32));
     have to_integer((at(output_b, b) % 65521u32)) <= 4294967295;
     have to_integer((at(output_b, b) % 65521u32)) < to_integer(65521u32);
     have to_integer((at(output_b, b) % 65521u32)) <= 65535 by close() using { to_integer((at(output_b, b) % 65521u32)) < 65521; };
     step_until(function.exit);
     have statement(22).call(0).result == 65521u32 by close();
     have self.a == ((at(output_a, a) % statement(22).call(0).result) as u16) by close();
     have self.a == ((at(output_a, a) % 65521u32) as u16) by { rewrite(self.a, ((at(output_a, a) % statement(22).call(0).result) as u16)); rewrite(statement(22).call(0).result, 65521u32); close(); }
     have to_integer(self.a) == to_integer((at(output_a, a) % 65521u32)) by { rewrite(self.a, ((at(output_a, a) % 65521u32) as u16)); close() using { 0 <= to_integer((at(output_a, a) % 65521u32)); to_integer((at(output_a, a) % 65521u32)) <= 65535; }; }
     have statement(23).call(0).result == 65521u32 by close();
     have self.b == ((at(output_b, b) % statement(23).call(0).result) as u16) by close();
     have self.b == ((at(output_b, b) % 65521u32) as u16) by { rewrite(self.b, ((at(output_b, b) % statement(23).call(0).result) as u16)); rewrite(statement(23).call(0).result, 65521u32); close(); }
     have to_integer(self.b) == to_integer((at(output_b, b) % 65521u32)) by { rewrite(self.b, ((at(output_b, b) % 65521u32) as u16)); close() using { 0 <= to_integer((at(output_b, b) % 65521u32)); to_integer((at(output_b, b) % 65521u32)) <= 65535; }; }
     have bytes[0] == old(bytes[0]) by close() using {};
     have old(adler_spec_a(bytes.as_ptr(), 1, 1)) == truncating_remainder(1 + to_integer(old((bytes[0] as i32))), 65521) by close();
     have old(adler_spec_b(bytes.as_ptr(), 1, 1, 0)) == truncating_remainder(1 + to_integer(old((bytes[0] as i32))), 65521) by close();
     have to_integer(self.a) == to_integer((1u32 + old((bytes[0] as u32))) % 65521u32) by {
     rewrite(to_integer(self.a), to_integer((at(output_a, a) % 65521u32)));
     rewrite((at(output_a, a) % 65521u32), (1u32 + old((bytes[0] as u32))) % 65521u32);
     close();
     }
     apply(integer::uint32_remainder_to_integer(1u32 + old((bytes[0] as u32)), 65521u32));
     have to_integer((1u32 + old((bytes[0] as u32))) % 65521u32) == truncating_remainder(to_integer(1u32 + old((bytes[0] as u32))), 65521) by close();
     have to_integer(1u32 + old((bytes[0] as u32))) == 1 + to_integer(old((bytes[0] as u32))) by close();
     have to_integer(self.a) == old(adler_spec_a(bytes.as_ptr(), 1, 1)) by {
     rewrite(to_integer(self.a), to_integer((1u32 + old((bytes[0] as u32))) % 65521u32));
     rewrite(to_integer((1u32 + old((bytes[0] as u32))) % 65521u32), truncating_remainder(to_integer(1u32 + old((bytes[0] as u32))), 65521));
     rewrite(to_integer(1u32 + old((bytes[0] as u32))), 1 + to_integer(old((bytes[0] as u32))));
     rewrite(old(adler_spec_a(bytes.as_ptr(), 1, 1)), truncating_remainder(1 + to_integer(old((bytes[0] as i32))), 65521));
     rewrite(to_integer(old((bytes[0] as u32))), to_integer(old((bytes[0] as i32))));
     close();
     }
     have to_integer(self.b) == to_integer((393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32) by {
     rewrite(to_integer(self.b), to_integer((at(output_b, b) % 65521u32)));
     rewrite((at(output_b, b) % 65521u32), (393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32);
     close();
     }
     apply(integer::uint32_remainder_to_integer(393126u32 + (1u32 + old((bytes[0] as u32))), 65521u32));
     have to_integer((393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32) == truncating_remainder(to_integer(393126u32 + (1u32 + old((bytes[0] as u32)))), 65521) by close();
     have to_integer(393126u32 + (1u32 + old((bytes[0] as u32)))) == 393126 + to_integer(1u32 + old((bytes[0] as u32))) by close();
     have to_integer(self.b) == old(adler_spec_b(bytes.as_ptr(), 1, 1, 0)) by {
     rewrite(to_integer(self.b), to_integer((393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32));
     rewrite(to_integer((393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32), truncating_remainder(to_integer(393126u32 + (1u32 + old((bytes[0] as u32)))), 65521));
     rewrite(to_integer(393126u32 + (1u32 + old((bytes[0] as u32)))), 393126 + to_integer(1u32 + old((bytes[0] as u32))));
     rewrite(to_integer(1u32 + old((bytes[0] as u32))), 1 + to_integer(old((bytes[0] as u32))));
     rewrite(truncating_remainder(393126 + (1 + to_integer(old((bytes[0] as u32)))), 65521), truncating_remainder(1 + to_integer(old((bytes[0] as u32))), 65521));
     rewrite(old(adler_spec_b(bytes.as_ptr(), 1, 1, 0)), truncating_remainder(1 + to_integer(old((bytes[0] as i32))), 65521));
     rewrite(to_integer(old((bytes[0] as u32))), to_integer(old((bytes[0] as i32))));
     close();
     }

     // Close the owned fields and the checked output equalities.
     close();
     close();
     close() using { to_integer(self.a) == to_integer((1u32 + old((bytes[0] as u32))) % 65521u32); };
     close() using { bytes[0] == old(bytes[0]); };
     close() using { to_integer(self.b) == to_integer((393126u32 + (1u32 + old((bytes[0] as u32)))) % 65521u32); };
     close() using { to_integer(self.a) == old(adler_spec_a(bytes.as_ptr(), 1, 1)); };
     close() using { to_integer(self.b) == old(adler_spec_b(bytes.as_ptr(), 1, 1, 0)); };
    }
}
