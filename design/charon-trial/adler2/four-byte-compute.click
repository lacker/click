// Four-byte boundary of the original, locked Adler32::compute body.
// The fixture harness combines this contract with the helper/getter contracts
// from helpers.click, checks all their bodies, and rechecks the proof tools.
impl adler2::Adler32 {
    fn compute(&mut self, bytes: &[u8]) {
     requires bytes.len() == 4u64;
     requires self.a == 1;
     requires self.b == 0;
     owns self.a;
     owns self.b;
     views bytes[0..4];
     ensures to_integer(self.a) == to_integer((((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32);
     ensures to_integer(self.b) == to_integer((((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32);
     ensures bytes[0] == old(bytes[0]);
     ensures bytes[1] == old(bytes[1]);
     ensures bytes[2] == old(bytes[2]);
     ensures bytes[3] == old(bytes[3]);
     ensures to_integer(self.a) == old(adler_spec_a(bytes, 4, 1));
     ensures to_integer(self.b) == old(adler_spec_b(bytes, 4, 1, 0));
    } by {
     apply(adler_four_byte_result_spec(bytes));
     have old(bytes.len()) == 4u64;
     execute_until(assignment(b, 0)); step();
     execute_until(assignment(remainder_chunk_len, 0)); step();
     have remainder_chunk_len == 4u64;
     mark input_batch;
     have at(input_batch, remainder_chunk_len) == 4u64 by simp() using { remainder_chunk_len == 4u64; };
     have at(input_batch, a) == 1u32;
     have at(input_batch, b) == 0u32;
     // Observe the stored int32 traversal state, not the uint64 slice facade.
     execute_until(loop(2));
     have __rust_mir_62_remaining == 4u64;
     have __rust_mir_62_remaining <= 4u64 by { rewrite(__rust_mir_62_remaining == 4u64); normalize(); }
     have ((__rust_mir_62_remaining as u32) as i32) == 4;
     have adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)) == 0 by {
      rewrite(((__rust_mir_62_remaining as u32) as i32) == 4);
      apply(adler_lane_iterator_initial(4)); assumption();
     }
     have viewable(bytes[0..4]) by {
      transport(at(function.entry, viewable(bytes[0..4])), viewable(bytes[0..4])) using { at(function.entry, viewable(bytes[0..4])); }
     }
     have __rust_mir_62_cursor == old(bytes) + (4 - ((__rust_mir_62_remaining as u32) as i32)) by {
      have __rust_mir_62_cursor == old(bytes);
      rewrite(((__rust_mir_62_remaining as u32) as i32) == 4); simp() using { __rust_mir_62_cursor == old(bytes); }
     }
     have ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[0] == 0u32 by { intro(); simp(); }
     have ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[0] == old((bytes[0] as u32)) by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 0) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 4; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 0); }
     have ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[0] == 0u32 by { intro(); simp(); }
     have ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[0] == old((bytes[0] as u32)) by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 0) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 4; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 0); }
     have ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[1] == 0u32 by { intro(); simp(); }
     have ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[1] == old((bytes[1] as u32)) by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 0) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 4; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 0); }
     have ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[1] == 0u32 by { intro(); simp(); }
     have ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[1] == old((bytes[1] as u32)) by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 0) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 4; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 0); }
     have ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[2] == 0u32 by { intro(); simp(); }
     have ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[2] == old((bytes[2] as u32)) by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 0) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 4; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 0); }
     have ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[2] == 0u32 by { intro(); simp(); }
     have ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[2] == old((bytes[2] as u32)) by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 0) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 4; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 0); }
     have ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[3] == 0u32 by { intro(); simp(); }
     have ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[3] == old((bytes[3] as u32)) by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 0) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 4; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 0); }
     have ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[3] == 0u32 by { intro(); simp(); }
     have ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[3] == old((bytes[3] as u32)) by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 0) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 4; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 0); }
     have a_vec.0[0] <= 255u32;
     have b_vec.0[0] <= 255u32;
     have a_vec.0[1] <= 255u32;
     have b_vec.0[1] <= 255u32;
     have a_vec.0[2] <= 255u32;
     have b_vec.0[2] <= 255u32;
     have a_vec.0[3] <= 255u32;
     have b_vec.0[3] <= 255u32;
     have 0 <= ((__rust_mir_62_remaining as u32) as i32) and ((__rust_mir_62_remaining as u32) as i32) <= 4 by { both { arithmetic() using { ((__rust_mir_62_remaining as u32) as i32) == 4; } } and { arithmetic() using { ((__rust_mir_62_remaining as u32) as i32) == 4; } } }
     have ((__rust_mir_62_remaining as u32) as i32) % 4 == 0 by { rewrite(((__rust_mir_62_remaining as u32) as i32) == 4); normalize(); }
     have bytes == old(bytes);
     have a == 1u32;
     have b == 0u32;
     have remainder_chunk_len == 4u64;
     have __rust_mir_62_size == 4u64;
     have __rust_mir_62_size == 4u64 and __rust_mir_62_remaining <= 4u64 by { both { assumption(); } and { assumption(); } }
     loop {
      decreases __rust_mir_62_remaining;
      owns a_vec.0[0..4];
      owns b_vec.0[0..4];
      views bytes[0..4];
      invariant viewable(bytes[0..4]);
      invariant bytes == old(bytes);
      invariant a == 1u32;
      invariant b == 0u32;
      invariant remainder_chunk_len == 4u64;
      invariant __rust_mir_62_size == 4u64 and __rust_mir_62_remaining <= 4u64;
      invariant 0 <= ((__rust_mir_62_remaining as u32) as i32) and ((__rust_mir_62_remaining as u32) as i32) <= 4;
      invariant ((__rust_mir_62_remaining as u32) as i32) % 4 == 0;
      invariant __rust_mir_62_cursor == old(bytes) + (4 - ((__rust_mir_62_remaining as u32) as i32));
      invariant ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[0] == 0u32;
      invariant ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[0] == old((bytes[0] as u32));
      invariant ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[0] == 0u32;
      invariant ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[0] == old((bytes[0] as u32));
      invariant ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[1] == 0u32;
      invariant ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[1] == old((bytes[1] as u32));
      invariant ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[1] == 0u32;
      invariant ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[1] == old((bytes[1] as u32));
      invariant ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[2] == 0u32;
      invariant ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[2] == old((bytes[2] as u32));
      invariant ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[2] == 0u32;
      invariant ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[2] == old((bytes[2] as u32));
      invariant ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[3] == 0u32;
      invariant ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[3] == old((bytes[3] as u32));
      invariant ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[3] == 0u32;
      invariant ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[3] == old((bytes[3] as u32));
      invariant a_vec.0[0] <= 255u32;
      invariant b_vec.0[0] <= 255u32;
      invariant a_vec.0[1] <= 255u32;
      invariant b_vec.0[1] <= 255u32;
      invariant a_vec.0[2] <= 255u32;
      invariant b_vec.0[2] <= 255u32;
      invariant a_vec.0[3] <= 255u32;
      invariant b_vec.0[3] <= 255u32;
      preserve by {
        have __rust_mir_62_size == 4u64;
        have __rust_mir_62_remaining <= 4u64;
        have 4u64 <= __rust_mir_62_remaining;
        have __rust_mir_62_remaining == 4u64 by arithmetic() using { 4u64 <= __rust_mir_62_remaining; __rust_mir_62_remaining <= 4u64; };
        have __rust_mir_62_remaining <= 22208u64 by arithmetic() using { __rust_mir_62_remaining <= 4u64; };
        apply(adler_count_lane_step(__rust_mir_62_remaining)) using { 4u64 <= __rust_mir_62_remaining; __rust_mir_62_remaining <= 22208u64; }
        have ((__rust_mir_62_remaining as u32) as i32) == 4 by arithmetic() using { 4 <= ((__rust_mir_62_remaining as u32) as i32); ((__rust_mir_62_remaining as u32) as i32) <= 4; };
        have __rust_mir_62_cursor == old(bytes);
        have a_vec.0[0] == 0u32;
        have b_vec.0[0] == 0u32;
        have a_vec.0[1] == 0u32;
        have b_vec.0[1] == 0u32;
        have a_vec.0[2] == 0u32;
        have b_vec.0[2] == 0u32;
        have a_vec.0[3] == 0u32;
        have b_vec.0[3] == 0u32;
       mark lane_head;
       have at(lane_head, viewable(bytes[0..4])) by simp() using { viewable(bytes[0..4]); };
       have at(lane_head, __rust_mir_62_cursor) == old(bytes) by simp() using { __rust_mir_62_cursor == old(bytes); };
       have at(lane_head, __rust_mir_62_size) == 4u64 by simp() using { __rust_mir_62_size == 4u64; };
       have at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4 by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 4; };
       have adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)) == 0 by {
        unfold(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)));
        have to_integer(((__rust_mir_62_remaining as u32) as i32)) == 4 by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 4; };
        have 4 - to_integer(((__rust_mir_62_remaining as u32) as i32)) == 0 by arithmetic() using { to_integer(((__rust_mir_62_remaining as u32) as i32)) == 4; };
        rewrite(4 - to_integer(((__rust_mir_62_remaining as u32) as i32)) == 0); normalize();
       }
       apply(adler_lane_initial_ceiling());
       have to_integer(a_vec.0[0]) == 0 by { rewrite(a_vec.0[0] == 0u32); normalize(); }
       have to_integer(a_vec.0[0]) <= 65520 by arithmetic() using { to_integer(a_vec.0[0]) == 0; };
       have to_integer(b_vec.0[0]) == 0 by { rewrite(b_vec.0[0] == 0u32); normalize(); }
       have to_integer(b_vec.0[0]) <= 65520 by arithmetic() using { to_integer(b_vec.0[0]) == 0; };
       apply(adler_lane_iterator_reduced_initial(4, a_vec.0[0], b_vec.0[0])) using { to_integer(a_vec.0[0]) <= 65520; to_integer(b_vec.0[0]) <= 65520; }
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by {
        rewrite(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)) == 0);
        simp() using { adler_lane_a_ceiling(0) == 65520; to_integer(a_vec.0[0]) <= 65520; }
       }
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by {
        rewrite(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)) == 0);
        simp() using { adler_lane_b_ceiling(0) == 65520; to_integer(b_vec.0[0]) <= 65520; }
       }
       have to_integer(a_vec.0[1]) == 0 by { rewrite(a_vec.0[1] == 0u32); normalize(); }
       have to_integer(a_vec.0[1]) <= 65520 by arithmetic() using { to_integer(a_vec.0[1]) == 0; };
       have to_integer(b_vec.0[1]) == 0 by { rewrite(b_vec.0[1] == 0u32); normalize(); }
       have to_integer(b_vec.0[1]) <= 65520 by arithmetic() using { to_integer(b_vec.0[1]) == 0; };
       apply(adler_lane_iterator_reduced_initial(4, a_vec.0[1], b_vec.0[1])) using { to_integer(a_vec.0[1]) <= 65520; to_integer(b_vec.0[1]) <= 65520; }
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by {
        rewrite(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)) == 0);
        simp() using { adler_lane_a_ceiling(0) == 65520; to_integer(a_vec.0[1]) <= 65520; }
       }
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by {
        rewrite(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)) == 0);
        simp() using { adler_lane_b_ceiling(0) == 65520; to_integer(b_vec.0[1]) <= 65520; }
       }
       have to_integer(a_vec.0[2]) == 0 by { rewrite(a_vec.0[2] == 0u32); normalize(); }
       have to_integer(a_vec.0[2]) <= 65520 by arithmetic() using { to_integer(a_vec.0[2]) == 0; };
       have to_integer(b_vec.0[2]) == 0 by { rewrite(b_vec.0[2] == 0u32); normalize(); }
       have to_integer(b_vec.0[2]) <= 65520 by arithmetic() using { to_integer(b_vec.0[2]) == 0; };
       apply(adler_lane_iterator_reduced_initial(4, a_vec.0[2], b_vec.0[2])) using { to_integer(a_vec.0[2]) <= 65520; to_integer(b_vec.0[2]) <= 65520; }
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by {
        rewrite(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)) == 0);
        simp() using { adler_lane_a_ceiling(0) == 65520; to_integer(a_vec.0[2]) <= 65520; }
       }
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by {
        rewrite(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)) == 0);
        simp() using { adler_lane_b_ceiling(0) == 65520; to_integer(b_vec.0[2]) <= 65520; }
       }
       have to_integer(a_vec.0[3]) == 0 by { rewrite(a_vec.0[3] == 0u32); normalize(); }
       have to_integer(a_vec.0[3]) <= 65520 by arithmetic() using { to_integer(a_vec.0[3]) == 0; };
       have to_integer(b_vec.0[3]) == 0 by { rewrite(b_vec.0[3] == 0u32); normalize(); }
       have to_integer(b_vec.0[3]) <= 65520 by arithmetic() using { to_integer(b_vec.0[3]) == 0; };
       apply(adler_lane_iterator_reduced_initial(4, a_vec.0[3], b_vec.0[3])) using { to_integer(a_vec.0[3]) <= 65520; to_integer(b_vec.0[3]) <= 65520; }
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by {
        rewrite(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)) == 0);
        simp() using { adler_lane_a_ceiling(0) == 65520; to_integer(a_vec.0[3]) <= 65520; }
       }
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by {
        rewrite(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32)) == 0);
        simp() using { adler_lane_b_ceiling(0) == 65520; to_integer(b_vec.0[3]) <= 65520; }
       }
       execute_until(assignment(__rust_mir_69, 0)); step();
       have __rust_mir_69 == old(bytes) by simp() using { at(lane_head, __rust_mir_62_cursor) == old(bytes); at(lane_head, __rust_mir_62_size) == 4u64; at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4; };
       execute_until(assignment(__rust_mir_71, 0));
       have __rust_mir_62_cursor == old(bytes) + 4 by simp() using { at(lane_head, __rust_mir_62_cursor) == old(bytes); at(lane_head, __rust_mir_62_size) == 4u64; at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4; };
       have ((__rust_mir_62_remaining as u32) as i32) == 0 by simp() using { at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4; at(lane_head, __rust_mir_62_size) == 4u64; };
       // next() consumes four bytes before either original helper call.
       have ((__rust_mir_62_remaining as u32) as i32) == at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4 by {
        rewrite(at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4); simp() using { ((__rust_mir_62_remaining as u32) as i32) == 0; }
       }
       have 0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) by arithmetic() using { at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4; };
       have 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) by arithmetic() using { at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4; };
       have at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4 by arithmetic() using { at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4; };
       have defined(at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4) by simp() using { at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4; };
       apply(adler_lane_iterator_successor(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        defined(at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4);
       }

       have adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) == 0 by {
        unfold(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        have to_integer(at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) == 4 by simp() using { at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4; };
        have 4 - to_integer(at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) == 0 by arithmetic() using { to_integer(at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) == 4; };
        rewrite(4 - to_integer(at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) == 0); normalize();
       }
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520 by {
        rewrite(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) == 0); simp() using { adler_lane_a_ceiling(0) == 65520; }
       }
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520 by {
        rewrite(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))) == 0); simp() using { adler_lane_b_ceiling(0) == 65520; }
       }

       have __rust_mir_69 == old(bytes) by simp() using { __rust_mir_62_cursor == old(bytes) + 4; };
       have __rust_mir_68.0[0] == __rust_mir_69[0];
       have __rust_mir_68.0[0] == old(bytes[0]) by simp() using { __rust_mir_68.0[0] == __rust_mir_69[0]; __rust_mir_69 == old(bytes); };
       have to_integer(__rust_mir_68.0[0]) <= 255;
       have to_integer(a_vec.0[0]) == 0 by { rewrite(a_vec.0[0] == 0u32); normalize(); }
       have to_integer(b_vec.0[0]) == 0 by { rewrite(b_vec.0[0] == 0u32); normalize(); }
       have 0 <= to_integer(__rust_mir_68.0[0]);
       have 0 <= to_integer(a_vec.0[0]) by arithmetic() using { to_integer(a_vec.0[0]) == 0; };
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[0]) == 0; adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520; };
       have 0 <= to_integer(b_vec.0[0]) by arithmetic() using { to_integer(b_vec.0[0]) == 0; };
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[0]) == 0; adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520; };
       apply(adler_lane_iterator_add_contracts(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), a_vec.0[0], b_vec.0[0], __rust_mir_68.0[0])) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(a_vec.0[0]); to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(b_vec.0[0]); to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(__rust_mir_68.0[0]); to_integer(__rust_mir_68.0[0]) <= 255;
        adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520;
        adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520;
       }
       have __rust_mir_68.0[1] == __rust_mir_69[1];
       have __rust_mir_68.0[1] == old(bytes[1]) by simp() using { __rust_mir_68.0[1] == __rust_mir_69[1]; __rust_mir_69 == old(bytes); };
       have to_integer(__rust_mir_68.0[1]) <= 255;
       have to_integer(a_vec.0[1]) == 0 by { rewrite(a_vec.0[1] == 0u32); normalize(); }
       have to_integer(b_vec.0[1]) == 0 by { rewrite(b_vec.0[1] == 0u32); normalize(); }
       have 0 <= to_integer(__rust_mir_68.0[1]);
       have 0 <= to_integer(a_vec.0[1]) by arithmetic() using { to_integer(a_vec.0[1]) == 0; };
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[1]) == 0; adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520; };
       have 0 <= to_integer(b_vec.0[1]) by arithmetic() using { to_integer(b_vec.0[1]) == 0; };
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[1]) == 0; adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520; };
       apply(adler_lane_iterator_add_contracts(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), a_vec.0[1], b_vec.0[1], __rust_mir_68.0[1])) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(a_vec.0[1]); to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(b_vec.0[1]); to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(__rust_mir_68.0[1]); to_integer(__rust_mir_68.0[1]) <= 255;
        adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520;
        adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520;
       }
       have __rust_mir_68.0[2] == __rust_mir_69[2];
       have __rust_mir_68.0[2] == old(bytes[2]) by simp() using { __rust_mir_68.0[2] == __rust_mir_69[2]; __rust_mir_69 == old(bytes); };
       have to_integer(__rust_mir_68.0[2]) <= 255;
       have to_integer(a_vec.0[2]) == 0 by { rewrite(a_vec.0[2] == 0u32); normalize(); }
       have to_integer(b_vec.0[2]) == 0 by { rewrite(b_vec.0[2] == 0u32); normalize(); }
       have 0 <= to_integer(__rust_mir_68.0[2]);
       have 0 <= to_integer(a_vec.0[2]) by arithmetic() using { to_integer(a_vec.0[2]) == 0; };
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[2]) == 0; adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520; };
       have 0 <= to_integer(b_vec.0[2]) by arithmetic() using { to_integer(b_vec.0[2]) == 0; };
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[2]) == 0; adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520; };
       apply(adler_lane_iterator_add_contracts(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), a_vec.0[2], b_vec.0[2], __rust_mir_68.0[2])) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(a_vec.0[2]); to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(b_vec.0[2]); to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(__rust_mir_68.0[2]); to_integer(__rust_mir_68.0[2]) <= 255;
        adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520;
        adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520;
       }
       have __rust_mir_68.0[3] == __rust_mir_69[3];
       have __rust_mir_68.0[3] == old(bytes[3]) by simp() using { __rust_mir_68.0[3] == __rust_mir_69[3]; __rust_mir_69 == old(bytes); };
       have to_integer(__rust_mir_68.0[3]) <= 255;
       have to_integer(a_vec.0[3]) == 0 by { rewrite(a_vec.0[3] == 0u32); normalize(); }
       have to_integer(b_vec.0[3]) == 0 by { rewrite(b_vec.0[3] == 0u32); normalize(); }
       have 0 <= to_integer(__rust_mir_68.0[3]);
       have 0 <= to_integer(a_vec.0[3]) by arithmetic() using { to_integer(a_vec.0[3]) == 0; };
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(a_vec.0[3]) == 0; adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520; };
       have 0 <= to_integer(b_vec.0[3]) by arithmetic() using { to_integer(b_vec.0[3]) == 0; };
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by arithmetic() using { to_integer(b_vec.0[3]) == 0; adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520; };
       apply(adler_lane_iterator_add_contracts(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), a_vec.0[3], b_vec.0[3], __rust_mir_68.0[3])) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(a_vec.0[3]); to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(b_vec.0[3]); to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(__rust_mir_68.0[3]); to_integer(__rust_mir_68.0[3]) <= 255;
        adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520;
        adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) == 65520;
       }
       mark vector_a;
       have at(vector_a, a_vec.0[0]) == 0u32;
       have at(vector_a, __rust_mir_68.0[0]) == old(bytes[0]) by simp() using { __rust_mir_68.0[0] == old(bytes[0]); };
       have to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255 by simp() using { to_integer(__rust_mir_68.0[0]) <= 255; };
       have at(vector_a, a_vec.0[1]) == 0u32;
       have at(vector_a, __rust_mir_68.0[1]) == old(bytes[1]) by simp() using { __rust_mir_68.0[1] == old(bytes[1]); };
       have to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255 by simp() using { to_integer(__rust_mir_68.0[1]) <= 255; };
       have at(vector_a, a_vec.0[2]) == 0u32;
       have at(vector_a, __rust_mir_68.0[2]) == old(bytes[2]) by simp() using { __rust_mir_68.0[2] == old(bytes[2]); };
       have to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255 by simp() using { to_integer(__rust_mir_68.0[2]) <= 255; };
       have at(vector_a, a_vec.0[3]) == 0u32;
       have at(vector_a, __rust_mir_68.0[3]) == old(bytes[3]) by simp() using { __rust_mir_68.0[3] == old(bytes[3]); };
       have to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255 by simp() using { to_integer(__rust_mir_68.0[3]) <= 255; };
       // Retain the entry lanes for both checked helper calls.
       have 0 <= to_integer(at(vector_a, a_vec.0[0]));
       have to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by simp() using { to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); };
       have 0 <= to_integer(at(vector_a, b_vec.0[0]));
       have to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by simp() using { to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); };
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[0]));
       apply(adler_lane_iterator_add_contracts(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_68.0[0]))) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(at(vector_a, a_vec.0[0])); to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, b_vec.0[0])); to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255;
       }
       apply(adler_lane_iterator_native_preservation(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), at(vector_a, a_vec.0[0]), at(vector_a, b_vec.0[0]), at(vector_a, __rust_mir_68.0[0]))) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(at(vector_a, a_vec.0[0])); to_integer(at(vector_a, a_vec.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, b_vec.0[0])); to_integer(at(vector_a, b_vec.0[0])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255;
       }
       have 0 <= to_integer(at(vector_a, a_vec.0[1]));
       have to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by simp() using { to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); };
       have 0 <= to_integer(at(vector_a, b_vec.0[1]));
       have to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by simp() using { to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); };
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[1]));
       apply(adler_lane_iterator_add_contracts(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_68.0[1]))) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(at(vector_a, a_vec.0[1])); to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, b_vec.0[1])); to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255;
       }
       apply(adler_lane_iterator_native_preservation(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), at(vector_a, a_vec.0[1]), at(vector_a, b_vec.0[1]), at(vector_a, __rust_mir_68.0[1]))) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(at(vector_a, a_vec.0[1])); to_integer(at(vector_a, a_vec.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, b_vec.0[1])); to_integer(at(vector_a, b_vec.0[1])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255;
       }
       have 0 <= to_integer(at(vector_a, a_vec.0[2]));
       have to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by simp() using { to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); };
       have 0 <= to_integer(at(vector_a, b_vec.0[2]));
       have to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by simp() using { to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); };
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[2]));
       apply(adler_lane_iterator_add_contracts(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_68.0[2]))) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(at(vector_a, a_vec.0[2])); to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, b_vec.0[2])); to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255;
       }
       apply(adler_lane_iterator_native_preservation(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), at(vector_a, a_vec.0[2]), at(vector_a, b_vec.0[2]), at(vector_a, __rust_mir_68.0[2]))) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(at(vector_a, a_vec.0[2])); to_integer(at(vector_a, a_vec.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, b_vec.0[2])); to_integer(at(vector_a, b_vec.0[2])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255;
       }
       have 0 <= to_integer(at(vector_a, a_vec.0[3]));
       have to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by simp() using { to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); };
       have 0 <= to_integer(at(vector_a, b_vec.0[3]));
       have to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))) by simp() using { to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)))); };
       have 0 <= to_integer(at(vector_a, __rust_mir_68.0[3]));
       apply(adler_lane_iterator_add_contracts(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[3]))) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(at(vector_a, a_vec.0[3])); to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, b_vec.0[3])); to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255;
       }
       apply(adler_lane_iterator_native_preservation(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)), at(vector_a, a_vec.0[3]), at(vector_a, b_vec.0[3]), at(vector_a, __rust_mir_68.0[3]))) using {
        0 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); 4 <= at(lane_head, ((__rust_mir_62_remaining as u32) as i32)); at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) <= 4;
        0 <= to_integer(at(vector_a, a_vec.0[3])); to_integer(at(vector_a, a_vec.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, b_vec.0[3])); to_integer(at(vector_a, b_vec.0[3])) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32))));
        0 <= to_integer(at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255;
       }
       execute_until(assignment(__rust_mir_74, 0));
       have a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]);
       have a_vec.0[0] == old(bytes[0]) by {
       rewrite(a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]));
       rewrite(at(vector_a, a_vec.0[0]) == 0u32);
       rewrite(at(vector_a, __rust_mir_68.0[0]) == old(bytes[0])); simp() using {};
       }
       have a_vec.0[0] == at(vector_a, __rust_mir_68.0[0]) by {
       rewrite(a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]));
       rewrite(at(vector_a, a_vec.0[0]) == 0u32); simp() using {};
       }
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, __rust_mir_68.0[0])) by simp() using { a_vec.0[0] == at(vector_a, __rust_mir_68.0[0]); };
       have to_integer(a_vec.0[0]) <= 255 by arithmetic() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, __rust_mir_68.0[0])) <= 255; };
       have to_integer(b_vec.0[0]) == 0 by { rewrite(b_vec.0[0] == 0u32); normalize(); }
       have b_vec.0[0] == at(vector_a, b_vec.0[0]);
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]); };
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) by simp() using { a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]); };
       have to_integer(b_vec.0[0]) + to_integer(a_vec.0[0]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0])); to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); to_integer(at(vector_a, b_vec.0[0])) + to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) <= 4294967295; };
       have a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]);
       have a_vec.0[1] == old(bytes[1]) by {
       rewrite(a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]));
       rewrite(at(vector_a, a_vec.0[1]) == 0u32);
       rewrite(at(vector_a, __rust_mir_68.0[1]) == old(bytes[1])); simp() using {};
       }
       have a_vec.0[1] == at(vector_a, __rust_mir_68.0[1]) by {
       rewrite(a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]));
       rewrite(at(vector_a, a_vec.0[1]) == 0u32); simp() using {};
       }
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, __rust_mir_68.0[1])) by simp() using { a_vec.0[1] == at(vector_a, __rust_mir_68.0[1]); };
       have to_integer(a_vec.0[1]) <= 255 by arithmetic() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, __rust_mir_68.0[1])) <= 255; };
       have to_integer(b_vec.0[1]) == 0 by { rewrite(b_vec.0[1] == 0u32); normalize(); }
       have b_vec.0[1] == at(vector_a, b_vec.0[1]);
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]); };
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]); };
       have to_integer(b_vec.0[1]) + to_integer(a_vec.0[1]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1])); to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); to_integer(at(vector_a, b_vec.0[1])) + to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) <= 4294967295; };
       have a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]);
       have a_vec.0[2] == old(bytes[2]) by {
       rewrite(a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]));
       rewrite(at(vector_a, a_vec.0[2]) == 0u32);
       rewrite(at(vector_a, __rust_mir_68.0[2]) == old(bytes[2])); simp() using {};
       }
       have a_vec.0[2] == at(vector_a, __rust_mir_68.0[2]) by {
       rewrite(a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]));
       rewrite(at(vector_a, a_vec.0[2]) == 0u32); simp() using {};
       }
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, __rust_mir_68.0[2])) by simp() using { a_vec.0[2] == at(vector_a, __rust_mir_68.0[2]); };
       have to_integer(a_vec.0[2]) <= 255 by arithmetic() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, __rust_mir_68.0[2])) <= 255; };
       have to_integer(b_vec.0[2]) == 0 by { rewrite(b_vec.0[2] == 0u32); normalize(); }
       have b_vec.0[2] == at(vector_a, b_vec.0[2]);
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]); };
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]); };
       have to_integer(b_vec.0[2]) + to_integer(a_vec.0[2]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2])); to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); to_integer(at(vector_a, b_vec.0[2])) + to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) <= 4294967295; };
       have a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]);
       have a_vec.0[3] == old(bytes[3]) by {
       rewrite(a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]));
       rewrite(at(vector_a, a_vec.0[3]) == 0u32);
       rewrite(at(vector_a, __rust_mir_68.0[3]) == old(bytes[3])); simp() using {};
       }
       have a_vec.0[3] == at(vector_a, __rust_mir_68.0[3]) by {
       rewrite(a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]));
       rewrite(at(vector_a, a_vec.0[3]) == 0u32); simp() using {};
       }
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, __rust_mir_68.0[3])) by simp() using { a_vec.0[3] == at(vector_a, __rust_mir_68.0[3]); };
       have to_integer(a_vec.0[3]) <= 255 by arithmetic() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, __rust_mir_68.0[3])) <= 255; };
       have to_integer(b_vec.0[3]) == 0 by { rewrite(b_vec.0[3] == 0u32); normalize(); }
       have b_vec.0[3] == at(vector_a, b_vec.0[3]);
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]); };
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]); };
       have to_integer(b_vec.0[3]) + to_integer(a_vec.0[3]) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3])); to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); to_integer(at(vector_a, b_vec.0[3])) + to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) <= 4294967295; };
       mark vector_b;
       have at(vector_b, b_vec.0[0]) == at(vector_a, b_vec.0[0]) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]); };
       have at(vector_b, a_vec.0[0]) == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]) by simp() using { a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]); };
       have at(vector_b, b_vec.0[1]) == at(vector_a, b_vec.0[1]) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]); };
       have at(vector_b, a_vec.0[1]) == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]); };
       have at(vector_b, b_vec.0[2]) == at(vector_a, b_vec.0[2]) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]); };
       have at(vector_b, a_vec.0[2]) == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]); };
       have at(vector_b, b_vec.0[3]) == at(vector_a, b_vec.0[3]) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]); };
       have at(vector_b, a_vec.0[3]) == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]); };

       have at(vector_b, b_vec.0[0]) == 0u32;
       have at(vector_b, a_vec.0[0]) == old(bytes[0]) by simp() using { a_vec.0[0] == old(bytes[0]); };
       have to_integer(at(vector_b, a_vec.0[0])) <= 255 by simp() using { to_integer(a_vec.0[0]) <= 255; };
       apply(uint32_to_integer_less_equal_implies_less_equal(at(vector_b, a_vec.0[0]), 255u32)) using { to_integer(at(vector_b, a_vec.0[0])) <= 255; }
       have at(vector_b, b_vec.0[1]) == 0u32;
       have at(vector_b, a_vec.0[1]) == old(bytes[1]) by simp() using { a_vec.0[1] == old(bytes[1]); };
       have to_integer(at(vector_b, a_vec.0[1])) <= 255 by simp() using { to_integer(a_vec.0[1]) <= 255; };
       apply(uint32_to_integer_less_equal_implies_less_equal(at(vector_b, a_vec.0[1]), 255u32)) using { to_integer(at(vector_b, a_vec.0[1])) <= 255; }
       have at(vector_b, b_vec.0[2]) == 0u32;
       have at(vector_b, a_vec.0[2]) == old(bytes[2]) by simp() using { a_vec.0[2] == old(bytes[2]); };
       have to_integer(at(vector_b, a_vec.0[2])) <= 255 by simp() using { to_integer(a_vec.0[2]) <= 255; };
       apply(uint32_to_integer_less_equal_implies_less_equal(at(vector_b, a_vec.0[2]), 255u32)) using { to_integer(at(vector_b, a_vec.0[2])) <= 255; }
       have at(vector_b, b_vec.0[3]) == 0u32;
       have at(vector_b, a_vec.0[3]) == old(bytes[3]) by simp() using { a_vec.0[3] == old(bytes[3]); };
       have to_integer(at(vector_b, a_vec.0[3])) <= 255 by simp() using { to_integer(a_vec.0[3]) <= 255; };
       apply(uint32_to_integer_less_equal_implies_less_equal(at(vector_b, a_vec.0[3]), 255u32)) using { to_integer(at(vector_b, a_vec.0[3])) <= 255; }
       execute_until(back_edge());
       have b_vec.0[0] == at(vector_b, b_vec.0[0]) + at(vector_b, a_vec.0[0]);
       have b_vec.0[0] == old(bytes[0]) by {
       rewrite(b_vec.0[0] == at(vector_b, b_vec.0[0]) + at(vector_b, a_vec.0[0]));
       rewrite(at(vector_b, b_vec.0[0]) == 0u32);
       rewrite(at(vector_b, a_vec.0[0]) == old(bytes[0])); simp() using {};
       }
       have b_vec.0[1] == at(vector_b, b_vec.0[1]) + at(vector_b, a_vec.0[1]);
       have b_vec.0[1] == old(bytes[1]) by {
       rewrite(b_vec.0[1] == at(vector_b, b_vec.0[1]) + at(vector_b, a_vec.0[1]));
       rewrite(at(vector_b, b_vec.0[1]) == 0u32);
       rewrite(at(vector_b, a_vec.0[1]) == old(bytes[1])); simp() using {};
       }
       have b_vec.0[2] == at(vector_b, b_vec.0[2]) + at(vector_b, a_vec.0[2]);
       have b_vec.0[2] == old(bytes[2]) by {
       rewrite(b_vec.0[2] == at(vector_b, b_vec.0[2]) + at(vector_b, a_vec.0[2]));
       rewrite(at(vector_b, b_vec.0[2]) == 0u32);
       rewrite(at(vector_b, a_vec.0[2]) == old(bytes[2])); simp() using {};
       }
       have b_vec.0[3] == at(vector_b, b_vec.0[3]) + at(vector_b, a_vec.0[3]);
       have b_vec.0[3] == old(bytes[3]) by {
       rewrite(b_vec.0[3] == at(vector_b, b_vec.0[3]) + at(vector_b, a_vec.0[3]));
       rewrite(at(vector_b, b_vec.0[3]) == 0u32);
       rewrite(at(vector_b, a_vec.0[3]) == old(bytes[3])); simp() using {};
       }
       // Both actual helper results satisfy the ceiling at next()'s new state.
       have ((__rust_mir_62_remaining as u32) as i32) == at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4;
       have adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)) by {
        rewrite(((__rust_mir_62_remaining as u32) as i32) == at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4); simp() using {};
       }
       have adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)) by {
        rewrite(((__rust_mir_62_remaining as u32) as i32) == at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4); simp() using {};
       }
       have a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]);
       have b_vec.0[0] == at(vector_b, b_vec.0[0]) + at(vector_b, a_vec.0[0]) by assumption();
       have b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) by simp() using { b_vec.0[0] == at(vector_b, b_vec.0[0]) + at(vector_b, a_vec.0[0]); at(vector_b, b_vec.0[0]) == at(vector_a, b_vec.0[0]); at(vector_b, a_vec.0[0]) == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]); };
       have to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) by simp() using { a_vec.0[0] == at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]); };
       have to_integer(a_vec.0[0]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { to_integer(a_vec.0[0]) == to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); to_integer(at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); };
       have to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) by simp() using { b_vec.0[0] == at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0])); };
       have to_integer(b_vec.0[0]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { to_integer(b_vec.0[0]) == to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); to_integer(at(vector_a, b_vec.0[0]) + (at(vector_a, a_vec.0[0]) + at(vector_a, __rust_mir_68.0[0]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); };
       have a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]);
       have b_vec.0[1] == at(vector_b, b_vec.0[1]) + at(vector_b, a_vec.0[1]) by assumption();
       have b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by simp() using { b_vec.0[1] == at(vector_b, b_vec.0[1]) + at(vector_b, a_vec.0[1]); at(vector_b, b_vec.0[1]) == at(vector_a, b_vec.0[1]); at(vector_b, a_vec.0[1]) == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]); };
       have to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) by simp() using { a_vec.0[1] == at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]); };
       have to_integer(a_vec.0[1]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { to_integer(a_vec.0[1]) == to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); to_integer(at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); };
       have to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) by simp() using { b_vec.0[1] == at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1])); };
       have to_integer(b_vec.0[1]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { to_integer(b_vec.0[1]) == to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); to_integer(at(vector_a, b_vec.0[1]) + (at(vector_a, a_vec.0[1]) + at(vector_a, __rust_mir_68.0[1]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); };
       have a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]);
       have b_vec.0[2] == at(vector_b, b_vec.0[2]) + at(vector_b, a_vec.0[2]) by assumption();
       have b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by simp() using { b_vec.0[2] == at(vector_b, b_vec.0[2]) + at(vector_b, a_vec.0[2]); at(vector_b, b_vec.0[2]) == at(vector_a, b_vec.0[2]); at(vector_b, a_vec.0[2]) == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]); };
       have to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) by simp() using { a_vec.0[2] == at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]); };
       have to_integer(a_vec.0[2]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { to_integer(a_vec.0[2]) == to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); to_integer(at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); };
       have to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) by simp() using { b_vec.0[2] == at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2])); };
       have to_integer(b_vec.0[2]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { to_integer(b_vec.0[2]) == to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); to_integer(at(vector_a, b_vec.0[2]) + (at(vector_a, a_vec.0[2]) + at(vector_a, __rust_mir_68.0[2]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); };
       have a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]);
       have b_vec.0[3] == at(vector_b, b_vec.0[3]) + at(vector_b, a_vec.0[3]) by assumption();
       have b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by simp() using { b_vec.0[3] == at(vector_b, b_vec.0[3]) + at(vector_b, a_vec.0[3]); at(vector_b, b_vec.0[3]) == at(vector_a, b_vec.0[3]); at(vector_b, a_vec.0[3]) == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]); };
       have to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) by simp() using { a_vec.0[3] == at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]); };
       have to_integer(a_vec.0[3]) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { to_integer(a_vec.0[3]) == to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); adler_lane_a_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) == adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); to_integer(at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])) <= adler_lane_a_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); };
       have to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) by simp() using { b_vec.0[3] == at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3])); };
       have to_integer(b_vec.0[3]) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) by arithmetic() using { to_integer(b_vec.0[3]) == to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))); adler_lane_b_ceiling(adler_lane_vectors_consumed(4, ((__rust_mir_62_remaining as u32) as i32))) == adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); to_integer(at(vector_a, b_vec.0[3]) + (at(vector_a, a_vec.0[3]) + at(vector_a, __rust_mir_68.0[3]))) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(4, at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) - 4)); };

       have a_vec.0[0] == old((bytes[0] as u32)) by simp() using { a_vec.0[0] == old(bytes[0]); };
       have b_vec.0[0] == old((bytes[0] as u32)) by simp() using { b_vec.0[0] == old(bytes[0]); };
       have a_vec.0[1] == old((bytes[1] as u32)) by simp() using { a_vec.0[1] == old(bytes[1]); };
       have b_vec.0[1] == old((bytes[1] as u32)) by simp() using { b_vec.0[1] == old(bytes[1]); };
       have a_vec.0[2] == old((bytes[2] as u32)) by simp() using { a_vec.0[2] == old(bytes[2]); };
       have b_vec.0[2] == old((bytes[2] as u32)) by simp() using { b_vec.0[2] == old(bytes[2]); };
       have a_vec.0[3] == old((bytes[3] as u32)) by simp() using { a_vec.0[3] == old(bytes[3]); };
       have b_vec.0[3] == old((bytes[3] as u32)) by simp() using { b_vec.0[3] == old(bytes[3]); };
       have viewable(bytes[0..4]) by simp() using { viewable(bytes[0..4]); };
       have bytes == old(bytes) by assumption();
       have __rust_mir_62_size == 4u64 by assumption();
       have 0 <= ((__rust_mir_62_remaining as u32) as i32) and ((__rust_mir_62_remaining as u32) as i32) <= 4 by { both { arithmetic() using { ((__rust_mir_62_remaining as u32) as i32) == 0; } } and { arithmetic() using { ((__rust_mir_62_remaining as u32) as i32) == 0; } } }
       have ((__rust_mir_62_remaining as u32) as i32) % 4 == 0 by { rewrite(((__rust_mir_62_remaining as u32) as i32) == 0); normalize(); }
       have __rust_mir_62_cursor == old(bytes) + (4 - ((__rust_mir_62_remaining as u32) as i32)) by { rewrite(((__rust_mir_62_remaining as u32) as i32) == 0); simp() using { __rust_mir_62_cursor == old(bytes) + 4; } }
       have ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[0] == 0u32 by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 4) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 0; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 4); }
       have ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[0] == old((bytes[0] as u32)) by { intro(); assumption(); }
       have ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[0] == 0u32 by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 4) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 0; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 4); }
       have ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[0] == old((bytes[0] as u32)) by { intro(); assumption(); }
       have ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[1] == 0u32 by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 4) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 0; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 4); }
       have ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[1] == old((bytes[1] as u32)) by { intro(); assumption(); }
       have ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[1] == 0u32 by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 4) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 0; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 4); }
       have ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[1] == old((bytes[1] as u32)) by { intro(); assumption(); }
       have ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[2] == 0u32 by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 4) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 0; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 4); }
       have ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[2] == old((bytes[2] as u32)) by { intro(); assumption(); }
       have ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[2] == 0u32 by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 4) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 0; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 4); }
       have ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[2] == old((bytes[2] as u32)) by { intro(); assumption(); }
       have ((__rust_mir_62_remaining as u32) as i32) == 4 implies a_vec.0[3] == 0u32 by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 4) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 0; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 4); }
       have ((__rust_mir_62_remaining as u32) as i32) == 0 implies a_vec.0[3] == old((bytes[3] as u32)) by { intro(); assumption(); }
       have ((__rust_mir_62_remaining as u32) as i32) == 4 implies b_vec.0[3] == 0u32 by { intro(); have not (((__rust_mir_62_remaining as u32) as i32) == 4) by simp() using { ((__rust_mir_62_remaining as u32) as i32) == 0; }; contradiction(((__rust_mir_62_remaining as u32) as i32) == 4); }
       have ((__rust_mir_62_remaining as u32) as i32) == 0 implies b_vec.0[3] == old((bytes[3] as u32)) by { intro(); assumption(); }
       have 0 <= ((__rust_mir_62_remaining as u32) as i32) by arithmetic() using { ((__rust_mir_62_remaining as u32) as i32) == 0; };
       have ((__rust_mir_62_remaining as u32) as i32) < at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) by { rewrite(((__rust_mir_62_remaining as u32) as i32) == 0); rewrite(at(lane_head, ((__rust_mir_62_remaining as u32) as i32)) == 4); simp() using {}; }
       have a_vec.0[0] <= 255u32 by simp() using { a_vec.0[0] == old(bytes[0]); at(vector_b, a_vec.0[0]) == old(bytes[0]); at(vector_b, a_vec.0[0]) <= 255u32; };
       have b_vec.0[0] <= 255u32 by simp() using { b_vec.0[0] == old(bytes[0]); at(vector_b, a_vec.0[0]) == old(bytes[0]); at(vector_b, a_vec.0[0]) <= 255u32; };
       have a_vec.0[1] <= 255u32 by simp() using { a_vec.0[1] == old(bytes[1]); at(vector_b, a_vec.0[1]) == old(bytes[1]); at(vector_b, a_vec.0[1]) <= 255u32; };
       have b_vec.0[1] <= 255u32 by simp() using { b_vec.0[1] == old(bytes[1]); at(vector_b, a_vec.0[1]) == old(bytes[1]); at(vector_b, a_vec.0[1]) <= 255u32; };
       have a_vec.0[2] <= 255u32 by simp() using { a_vec.0[2] == old(bytes[2]); at(vector_b, a_vec.0[2]) == old(bytes[2]); at(vector_b, a_vec.0[2]) <= 255u32; };
       have b_vec.0[2] <= 255u32 by simp() using { b_vec.0[2] == old(bytes[2]); at(vector_b, a_vec.0[2]) == old(bytes[2]); at(vector_b, a_vec.0[2]) <= 255u32; };
       have a_vec.0[3] <= 255u32 by simp() using { a_vec.0[3] == old(bytes[3]); at(vector_b, a_vec.0[3]) == old(bytes[3]); at(vector_b, a_vec.0[3]) <= 255u32; };
       have b_vec.0[3] <= 255u32 by simp() using { b_vec.0[3] == old(bytes[3]); at(vector_b, a_vec.0[3]) == old(bytes[3]); at(vector_b, a_vec.0[3]) <= 255u32; };
       have __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64;
       have 4u64 <= at(lane_head, __rust_mir_62_remaining);
       have at(lane_head, __rust_mir_62_remaining) <= 4u64;
       have __rust_mir_62_remaining <= 4u64 by arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); at(lane_head, __rust_mir_62_remaining) <= 4u64; };
       have __rust_mir_62_remaining < at(lane_head, __rust_mir_62_remaining) by arithmetic() using { __rust_mir_62_remaining == at(lane_head, __rust_mir_62_remaining) - 4u64; 4u64 <= at(lane_head, __rust_mir_62_remaining); };
       have __rust_mir_62_size == 4u64;
       have __rust_mir_62_size == 4u64 and __rust_mir_62_remaining <= 4u64 by { both { assumption(); } and { assumption(); } }
       close_invariants by {
        both {
         both {
          both {
           both {
            both {
             intro();
             assumption();
            } and {
             intro();
             intro();
             assumption();
            }
           } and {
            both {
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           }
          } and {
           both {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           } and {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           }
          }
         } and {
          both {
           both {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           } and {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           }
          } and {
           both {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           } and {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           }
          }
         }
        } and {
         both {
          both {
           both {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           } and {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           }
          } and {
           both {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           } and {
            both {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            } and {
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             intro();
             assumption();
            }
           }
          }
         } and {
          both {
           both {
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            intro();
            assumption();
           } and {
            normalize();
           }
          } and {
           assumption();
          }
         }
        }
       }
      }
     }
     have __rust_mir_62_remaining < 4u64 by { cases { not (0u64 < __rust_mir_62_remaining) => { arithmetic() using { not 0u64 < __rust_mir_62_remaining; } } not (4u64 <= __rust_mir_62_remaining) => { assumption(); } } }
     have __rust_mir_62_remaining <= 3u64 by arithmetic() using { __rust_mir_62_remaining < 4u64; };
     have 3u64 <= 22208u64 by normalize();
     have ((__rust_mir_62_remaining as u32) as i32) <= 3 by { apply(adler_count_at_least(3u64, __rust_mir_62_remaining)) using { __rust_mir_62_remaining <= 3u64; 3u64 <= 22208u64; } normalize() using { ((__rust_mir_62_remaining as u32) as i32) <= ((3u64 as u32) as i32); } }
     have ((__rust_mir_62_remaining as u32) as i32) < 4 by arithmetic() using { ((__rust_mir_62_remaining as u32) as i32) <= 3; };
     have ((__rust_mir_62_remaining as u32) as i32) % 4 == ((__rust_mir_62_remaining as u32) as i32) by normalize() using { 0 <= ((__rust_mir_62_remaining as u32) as i32); ((__rust_mir_62_remaining as u32) as i32) < 4; };
     have ((__rust_mir_62_remaining as u32) as i32) == 0;
     have __rust_mir_62_remaining <= 22208u64 by arithmetic() using { __rust_mir_62_remaining <= 3u64; };
     apply(adler_count_zero(__rust_mir_62_remaining)) using { __rust_mir_62_remaining <= 22208u64; ((__rust_mir_62_remaining as u32) as i32) == 0; }
     have a_vec.0[0] == old((bytes[0] as u32));
     have b_vec.0[0] == old((bytes[0] as u32));
     have a_vec.0[1] == old((bytes[1] as u32));
     have b_vec.0[1] == old((bytes[1] as u32));
     have a_vec.0[2] == old((bytes[2] as u32));
     have b_vec.0[2] == old((bytes[2] as u32));
     have a_vec.0[3] == old((bytes[3] as u32));
     have b_vec.0[3] == old((bytes[3] as u32));
     execute_until(assignment(__rust_mir_77, 0));
     have __rust_mir_78 == at(input_batch, remainder_chunk_len) by simp() using {};
     have __rust_mir_78 == 4u64 by {
      rewrite(__rust_mir_78 == at(input_batch, remainder_chunk_len));
      simp() using { at(input_batch, remainder_chunk_len) == 4u64; }
     }
     mark scalar_inputs;
     have at(scalar_inputs, __rust_mir_78) == 4u64 by simp() using { __rust_mir_78 == 4u64; };
     have at(scalar_inputs, a) == 1u32 by simp() using { at(input_batch, a) == 1u32; };
     have at(scalar_inputs, b) == 0u32 by simp() using { at(input_batch, b) == 0u32; };
     execute_until(assignment(b, 3)); step();
     have b == 4u32 by simp() using { at(scalar_inputs, __rust_mir_78) == 4u64; at(scalar_inputs, a) == 1u32; at(scalar_inputs, b) == 0u32; };
     mark vector_mod;
     have a_vec.0[0] == old((bytes[0] as u32));
     have at(vector_mod, a_vec.0[0]) == old(bytes[0]) by simp() using { a_vec.0[0] == old((bytes[0] as u32)); old((bytes[0] as u32)) == old(bytes[0]); };
     have a_vec.0[0] == old((bytes[0] as u32));
     have a_vec.0[0] <= 255u32 by assumption();
     have at(vector_mod, a_vec.0[0]) <= 255u32 by simp() using { a_vec.0[0] <= 255u32; };
     have at(vector_mod, a_vec.0[0]) < 65521u32 by arithmetic() using { at(vector_mod, a_vec.0[0]) <= 255u32; };
     have at(vector_mod, a_vec.0[1]) == old(bytes[1]) by simp() using { a_vec.0[1] == old(bytes[1]); };
     have a_vec.0[1] == old((bytes[1] as u32));
     have a_vec.0[1] <= 255u32 by assumption();
     have at(vector_mod, a_vec.0[1]) <= 255u32 by simp() using { a_vec.0[1] <= 255u32; };
     have at(vector_mod, a_vec.0[1]) < 65521u32 by arithmetic() using { at(vector_mod, a_vec.0[1]) <= 255u32; };
     have at(vector_mod, a_vec.0[2]) == old(bytes[2]) by simp() using { a_vec.0[2] == old(bytes[2]); };
     have a_vec.0[2] == old((bytes[2] as u32));
     have a_vec.0[2] <= 255u32 by assumption();
     have at(vector_mod, a_vec.0[2]) <= 255u32 by simp() using { a_vec.0[2] <= 255u32; };
     have at(vector_mod, a_vec.0[2]) < 65521u32 by arithmetic() using { at(vector_mod, a_vec.0[2]) <= 255u32; };
     have at(vector_mod, a_vec.0[3]) == old(bytes[3]) by simp() using { a_vec.0[3] == old(bytes[3]); };
     have a_vec.0[3] == old((bytes[3] as u32));
     have a_vec.0[3] <= 255u32 by assumption();
     have at(vector_mod, a_vec.0[3]) <= 255u32 by simp() using { a_vec.0[3] <= 255u32; };
     have at(vector_mod, a_vec.0[3]) < 65521u32 by arithmetic() using { at(vector_mod, a_vec.0[3]) <= 255u32; };
     have at(vector_mod, b_vec.0[0]) == old(bytes[0]) by simp() using { b_vec.0[0] == old(bytes[0]); };
     have b_vec.0[0] == old((bytes[0] as u32)) by {
     rewrite(b_vec.0[0] == 0u32 + old((bytes[0] as u32)));
     rewrite(0u32 == 0u32); simp() using {};
     }
     have b_vec.0[0] <= 255u32 by assumption();
     have at(vector_mod, b_vec.0[0]) <= 255u32 by simp() using { b_vec.0[0] <= 255u32; };
     have at(vector_mod, b_vec.0[0]) < 65521u32 by arithmetic() using { at(vector_mod, b_vec.0[0]) <= 255u32; };
     have at(vector_mod, b_vec.0[1]) == old(bytes[1]) by simp() using { b_vec.0[1] == old(bytes[1]); };
     have b_vec.0[1] == old((bytes[1] as u32)) by {
     rewrite(b_vec.0[1] == 0u32 + old((bytes[1] as u32)));
     rewrite(0u32 == 0u32); simp() using {};
     }
     have b_vec.0[1] <= 255u32 by assumption();
     have at(vector_mod, b_vec.0[1]) <= 255u32 by simp() using { b_vec.0[1] <= 255u32; };
     have at(vector_mod, b_vec.0[1]) < 65521u32 by arithmetic() using { at(vector_mod, b_vec.0[1]) <= 255u32; };
     have at(vector_mod, b_vec.0[2]) == old(bytes[2]) by simp() using { b_vec.0[2] == old(bytes[2]); };
     have b_vec.0[2] == old((bytes[2] as u32)) by {
     rewrite(b_vec.0[2] == 0u32 + old((bytes[2] as u32)));
     rewrite(0u32 == 0u32); simp() using {};
     }
     have b_vec.0[2] <= 255u32 by assumption();
     have at(vector_mod, b_vec.0[2]) <= 255u32 by simp() using { b_vec.0[2] <= 255u32; };
     have at(vector_mod, b_vec.0[2]) < 65521u32 by arithmetic() using { at(vector_mod, b_vec.0[2]) <= 255u32; };
     have at(vector_mod, b_vec.0[3]) == old(bytes[3]) by simp() using { b_vec.0[3] == old(bytes[3]); };
     have b_vec.0[3] == old((bytes[3] as u32)) by {
     rewrite(b_vec.0[3] == 0u32 + old((bytes[3] as u32)));
     rewrite(0u32 == 0u32); simp() using {};
     }
     have b_vec.0[3] <= 255u32 by assumption();
     have at(vector_mod, b_vec.0[3]) <= 255u32 by simp() using { b_vec.0[3] <= 255u32; };
     have at(vector_mod, b_vec.0[3]) < 65521u32 by arithmetic() using { at(vector_mod, b_vec.0[3]) <= 255u32; };
     execute_until(assignment(__rust_mir_84, 0));
     step();
     mark reduction_a;
     have at(reduction_a, a_vec.0[0]) == at(vector_mod, a_vec.0[0]);
     execute_until(assignment(__rust_mir_86, 0));
     have __rust_checked_84 == 65521u32;
     have at(reduction_a, a_vec.0[0]) < 65521u32 by { rewrite(at(reduction_a, a_vec.0[0]) == at(vector_mod, a_vec.0[0])); simp() using { at(vector_mod, a_vec.0[0]) < 65521u32; } }
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % __rust_checked_84 by simp() using { a_vec.0[0] == at(reduction_a, a_vec.0[0]) % __rust_checked_84; };
     have a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32 by { rewrite(a_vec.0[0] == at(reduction_a, a_vec.0[0]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
     apply(uint32_less_than_divisor_implies_remainder_is_value(at(reduction_a, a_vec.0[0]), 65521u32)) using { at(reduction_a, a_vec.0[0]) < 65521u32; }
     have a_vec.0[0] == at(vector_mod, a_vec.0[0]) by { rewrite(a_vec.0[0] == at(reduction_a, a_vec.0[0]) % 65521u32); rewrite(at(reduction_a, a_vec.0[0]) % 65521u32 == at(reduction_a, a_vec.0[0])); simp() using { at(reduction_a, a_vec.0[0]) == at(vector_mod, a_vec.0[0]); } }
     have a_vec.0[0] == old(bytes[0]) by { rewrite(a_vec.0[0] == at(vector_mod, a_vec.0[0])); simp() using { at(vector_mod, a_vec.0[0]) == old(bytes[0]); } }
     have at(reduction_a, a_vec.0[1]) == at(vector_mod, a_vec.0[1]);
     have at(reduction_a, a_vec.0[1]) < 65521u32 by { rewrite(at(reduction_a, a_vec.0[1]) == at(vector_mod, a_vec.0[1])); simp() using { at(vector_mod, a_vec.0[1]) < 65521u32; } }
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % __rust_checked_84 by simp() using { a_vec.0[1] == at(reduction_a, a_vec.0[1]) % __rust_checked_84; };
     have a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32 by { rewrite(a_vec.0[1] == at(reduction_a, a_vec.0[1]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
     apply(uint32_less_than_divisor_implies_remainder_is_value(at(reduction_a, a_vec.0[1]), 65521u32)) using { at(reduction_a, a_vec.0[1]) < 65521u32; }
     have a_vec.0[1] == at(vector_mod, a_vec.0[1]) by { rewrite(a_vec.0[1] == at(reduction_a, a_vec.0[1]) % 65521u32); rewrite(at(reduction_a, a_vec.0[1]) % 65521u32 == at(reduction_a, a_vec.0[1])); simp() using { at(reduction_a, a_vec.0[1]) == at(vector_mod, a_vec.0[1]); } }
     have a_vec.0[1] == old(bytes[1]) by { rewrite(a_vec.0[1] == at(vector_mod, a_vec.0[1])); simp() using { at(vector_mod, a_vec.0[1]) == old(bytes[1]); } }
     have at(reduction_a, a_vec.0[2]) == at(vector_mod, a_vec.0[2]);
     have at(reduction_a, a_vec.0[2]) < 65521u32 by { rewrite(at(reduction_a, a_vec.0[2]) == at(vector_mod, a_vec.0[2])); simp() using { at(vector_mod, a_vec.0[2]) < 65521u32; } }
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % __rust_checked_84 by simp() using { a_vec.0[2] == at(reduction_a, a_vec.0[2]) % __rust_checked_84; };
     have a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32 by { rewrite(a_vec.0[2] == at(reduction_a, a_vec.0[2]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
     apply(uint32_less_than_divisor_implies_remainder_is_value(at(reduction_a, a_vec.0[2]), 65521u32)) using { at(reduction_a, a_vec.0[2]) < 65521u32; }
     have a_vec.0[2] == at(vector_mod, a_vec.0[2]) by { rewrite(a_vec.0[2] == at(reduction_a, a_vec.0[2]) % 65521u32); rewrite(at(reduction_a, a_vec.0[2]) % 65521u32 == at(reduction_a, a_vec.0[2])); simp() using { at(reduction_a, a_vec.0[2]) == at(vector_mod, a_vec.0[2]); } }
     have a_vec.0[2] == old(bytes[2]) by { rewrite(a_vec.0[2] == at(vector_mod, a_vec.0[2])); simp() using { at(vector_mod, a_vec.0[2]) == old(bytes[2]); } }
     have at(reduction_a, a_vec.0[3]) == at(vector_mod, a_vec.0[3]);
     have at(reduction_a, a_vec.0[3]) < 65521u32 by { rewrite(at(reduction_a, a_vec.0[3]) == at(vector_mod, a_vec.0[3])); simp() using { at(vector_mod, a_vec.0[3]) < 65521u32; } }
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % __rust_checked_84 by simp() using { a_vec.0[3] == at(reduction_a, a_vec.0[3]) % __rust_checked_84; };
     have a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32 by { rewrite(a_vec.0[3] == at(reduction_a, a_vec.0[3]) % __rust_checked_84); simp() using { __rust_checked_84 == 65521u32; } }
     apply(uint32_less_than_divisor_implies_remainder_is_value(at(reduction_a, a_vec.0[3]), 65521u32)) using { at(reduction_a, a_vec.0[3]) < 65521u32; }
     have a_vec.0[3] == at(vector_mod, a_vec.0[3]) by { rewrite(a_vec.0[3] == at(reduction_a, a_vec.0[3]) % 65521u32); rewrite(at(reduction_a, a_vec.0[3]) % 65521u32 == at(reduction_a, a_vec.0[3])); simp() using { at(reduction_a, a_vec.0[3]) == at(vector_mod, a_vec.0[3]); } }
     have a_vec.0[3] == old(bytes[3]) by { rewrite(a_vec.0[3] == at(vector_mod, a_vec.0[3])); simp() using { at(vector_mod, a_vec.0[3]) == old(bytes[3]); } }
     step();
     mark reduction_b;
     have at(reduction_b, b_vec.0[0]) == at(vector_mod, b_vec.0[0]);
     execute_until(assignment(b, 4));
     have __rust_checked_81 == 65521u32;
     have at(reduction_b, b_vec.0[0]) < 65521u32 by { rewrite(at(reduction_b, b_vec.0[0]) == at(vector_mod, b_vec.0[0])); simp() using { at(vector_mod, b_vec.0[0]) < 65521u32; } }
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % __rust_checked_81 by simp() using { b_vec.0[0] == at(reduction_b, b_vec.0[0]) % __rust_checked_81; };
     have b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32 by { rewrite(b_vec.0[0] == at(reduction_b, b_vec.0[0]) % __rust_checked_81); simp() using { __rust_checked_81 == 65521u32; } }
     apply(uint32_less_than_divisor_implies_remainder_is_value(at(reduction_b, b_vec.0[0]), 65521u32)) using { at(reduction_b, b_vec.0[0]) < 65521u32; }
     have b_vec.0[0] == at(vector_mod, b_vec.0[0]) by { rewrite(b_vec.0[0] == at(reduction_b, b_vec.0[0]) % 65521u32); rewrite(at(reduction_b, b_vec.0[0]) % 65521u32 == at(reduction_b, b_vec.0[0])); simp() using { at(reduction_b, b_vec.0[0]) == at(vector_mod, b_vec.0[0]); } }
     have b_vec.0[0] == old(bytes[0]) by { rewrite(b_vec.0[0] == at(vector_mod, b_vec.0[0])); simp() using { at(vector_mod, b_vec.0[0]) == old(bytes[0]); } }
     have at(reduction_b, b_vec.0[1]) == at(vector_mod, b_vec.0[1]);
     have at(reduction_b, b_vec.0[1]) < 65521u32 by { rewrite(at(reduction_b, b_vec.0[1]) == at(vector_mod, b_vec.0[1])); simp() using { at(vector_mod, b_vec.0[1]) < 65521u32; } }
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % __rust_checked_81 by simp() using { b_vec.0[1] == at(reduction_b, b_vec.0[1]) % __rust_checked_81; };
     have b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32 by { rewrite(b_vec.0[1] == at(reduction_b, b_vec.0[1]) % __rust_checked_81); simp() using { __rust_checked_81 == 65521u32; } }
     apply(uint32_less_than_divisor_implies_remainder_is_value(at(reduction_b, b_vec.0[1]), 65521u32)) using { at(reduction_b, b_vec.0[1]) < 65521u32; }
     have b_vec.0[1] == at(vector_mod, b_vec.0[1]) by { rewrite(b_vec.0[1] == at(reduction_b, b_vec.0[1]) % 65521u32); rewrite(at(reduction_b, b_vec.0[1]) % 65521u32 == at(reduction_b, b_vec.0[1])); simp() using { at(reduction_b, b_vec.0[1]) == at(vector_mod, b_vec.0[1]); } }
     have b_vec.0[1] == old(bytes[1]) by { rewrite(b_vec.0[1] == at(vector_mod, b_vec.0[1])); simp() using { at(vector_mod, b_vec.0[1]) == old(bytes[1]); } }
     have at(reduction_b, b_vec.0[2]) == at(vector_mod, b_vec.0[2]);
     have at(reduction_b, b_vec.0[2]) < 65521u32 by { rewrite(at(reduction_b, b_vec.0[2]) == at(vector_mod, b_vec.0[2])); simp() using { at(vector_mod, b_vec.0[2]) < 65521u32; } }
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % __rust_checked_81 by simp() using { b_vec.0[2] == at(reduction_b, b_vec.0[2]) % __rust_checked_81; };
     have b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32 by { rewrite(b_vec.0[2] == at(reduction_b, b_vec.0[2]) % __rust_checked_81); simp() using { __rust_checked_81 == 65521u32; } }
     apply(uint32_less_than_divisor_implies_remainder_is_value(at(reduction_b, b_vec.0[2]), 65521u32)) using { at(reduction_b, b_vec.0[2]) < 65521u32; }
     have b_vec.0[2] == at(vector_mod, b_vec.0[2]) by { rewrite(b_vec.0[2] == at(reduction_b, b_vec.0[2]) % 65521u32); rewrite(at(reduction_b, b_vec.0[2]) % 65521u32 == at(reduction_b, b_vec.0[2])); simp() using { at(reduction_b, b_vec.0[2]) == at(vector_mod, b_vec.0[2]); } }
     have b_vec.0[2] == old(bytes[2]) by { rewrite(b_vec.0[2] == at(vector_mod, b_vec.0[2])); simp() using { at(vector_mod, b_vec.0[2]) == old(bytes[2]); } }
     have at(reduction_b, b_vec.0[3]) == at(vector_mod, b_vec.0[3]);
     have at(reduction_b, b_vec.0[3]) < 65521u32 by { rewrite(at(reduction_b, b_vec.0[3]) == at(vector_mod, b_vec.0[3])); simp() using { at(vector_mod, b_vec.0[3]) < 65521u32; } }
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % __rust_checked_81 by simp() using { b_vec.0[3] == at(reduction_b, b_vec.0[3]) % __rust_checked_81; };
     have b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32 by { rewrite(b_vec.0[3] == at(reduction_b, b_vec.0[3]) % __rust_checked_81); simp() using { __rust_checked_81 == 65521u32; } }
     apply(uint32_less_than_divisor_implies_remainder_is_value(at(reduction_b, b_vec.0[3]), 65521u32)) using { at(reduction_b, b_vec.0[3]) < 65521u32; }
     have b_vec.0[3] == at(vector_mod, b_vec.0[3]) by { rewrite(b_vec.0[3] == at(reduction_b, b_vec.0[3]) % 65521u32); rewrite(at(reduction_b, b_vec.0[3]) % 65521u32 == at(reduction_b, b_vec.0[3])); simp() using { at(reduction_b, b_vec.0[3]) == at(vector_mod, b_vec.0[3]); } }
     have b_vec.0[3] == old(bytes[3]) by { rewrite(b_vec.0[3] == at(vector_mod, b_vec.0[3])); simp() using { at(vector_mod, b_vec.0[3]) == old(bytes[3]); } }
     mark scalar_mod;
     have at(scalar_mod, __rust_checked_77) == 4u32 by simp() using { at(scalar_inputs, __rust_mir_78) == 4u64; at(scalar_inputs, a) == 1u32; at(scalar_inputs, b) == 0u32; };
     have at(scalar_mod, __rust_checked_79) == 65521u32;
     step();
     have b == at(scalar_mod, __rust_checked_77) % at(scalar_mod, __rust_checked_79) by simp() using {};
     have b == 4u32 by { rewrite(b == at(scalar_mod, __rust_checked_77) % at(scalar_mod, __rust_checked_79)); rewrite(at(scalar_mod, __rust_checked_77) == 4u32); rewrite(at(scalar_mod, __rust_checked_79) == 65521u32); simp() using {}; }
     have b_vec.0[0] <= 255u32 by { rewrite(b_vec.0[0] == at(vector_mod, b_vec.0[0])); simp() using { at(vector_mod, b_vec.0[0]) <= 255u32; } }
     have b_vec.0[0] <= 4294967295u32 / 4u32 by arithmetic() using { b_vec.0[0] <= 255u32; };
     have b_vec.0[1] <= 255u32 by { rewrite(b_vec.0[1] == at(vector_mod, b_vec.0[1])); simp() using { at(vector_mod, b_vec.0[1]) <= 255u32; } }
     have b_vec.0[1] <= 4294967295u32 / 4u32 by arithmetic() using { b_vec.0[1] <= 255u32; };
     have b_vec.0[2] <= 255u32 by { rewrite(b_vec.0[2] == at(vector_mod, b_vec.0[2])); simp() using { at(vector_mod, b_vec.0[2]) <= 255u32; } }
     have b_vec.0[2] <= 4294967295u32 / 4u32 by arithmetic() using { b_vec.0[2] <= 255u32; };
     have b_vec.0[3] <= 255u32 by { rewrite(b_vec.0[3] == at(vector_mod, b_vec.0[3])); simp() using { at(vector_mod, b_vec.0[3]) <= 255u32; } }
     have b_vec.0[3] <= 4294967295u32 / 4u32 by arithmetic() using { b_vec.0[3] <= 255u32; };
     execute_until(assignment(__rust_mir_88, 0));
     step();
     mark weighted_b;
     execute_until(assignment(__rust_mir_89, 0));
     have b_vec.0[0] == at(weighted_b, b_vec.0[0]) * 4u32;
     have b_vec.0[1] == at(weighted_b, b_vec.0[1]) * 4u32;
     have b_vec.0[2] == at(weighted_b, b_vec.0[2]) * 4u32;
     have b_vec.0[3] == at(weighted_b, b_vec.0[3]) * 4u32;
     have at(weighted_b, b_vec.0[0]) <= 255u32;
     apply(uint32_less_equal_to_integer(at(weighted_b, b_vec.0[0]), 255u32)) using { at(weighted_b, b_vec.0[0]) <= 255u32; }
     have to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4;
     have to_integer(b_vec.0[0]) <= 1020 by arithmetic() using { to_integer(b_vec.0[0]) == to_integer(at(weighted_b, b_vec.0[0])) * 4; to_integer(at(weighted_b, b_vec.0[0])) <= 255; };
     have a_vec.0[0] <= 255u32 by { rewrite(a_vec.0[0] == at(vector_mod, a_vec.0[0])); simp() using { at(vector_mod, a_vec.0[0]) <= 255u32; } }
     have a_vec.0[0] <= 65521u32 by arithmetic() using { a_vec.0[0] <= 255u32; };
     have at(weighted_b, b_vec.0[1]) <= 255u32;
     apply(uint32_less_equal_to_integer(at(weighted_b, b_vec.0[1]), 255u32)) using { at(weighted_b, b_vec.0[1]) <= 255u32; }
     have to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4;
     have to_integer(b_vec.0[1]) <= 1020 by arithmetic() using { to_integer(b_vec.0[1]) == to_integer(at(weighted_b, b_vec.0[1])) * 4; to_integer(at(weighted_b, b_vec.0[1])) <= 255; };
     have a_vec.0[1] <= 255u32 by { rewrite(a_vec.0[1] == at(vector_mod, a_vec.0[1])); simp() using { at(vector_mod, a_vec.0[1]) <= 255u32; } }
     have a_vec.0[1] <= 65521u32 by arithmetic() using { a_vec.0[1] <= 255u32; };
     have at(weighted_b, b_vec.0[2]) <= 255u32;
     apply(uint32_less_equal_to_integer(at(weighted_b, b_vec.0[2]), 255u32)) using { at(weighted_b, b_vec.0[2]) <= 255u32; }
     have to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4;
     have to_integer(b_vec.0[2]) <= 1020 by arithmetic() using { to_integer(b_vec.0[2]) == to_integer(at(weighted_b, b_vec.0[2])) * 4; to_integer(at(weighted_b, b_vec.0[2])) <= 255; };
     have a_vec.0[2] <= 255u32 by { rewrite(a_vec.0[2] == at(vector_mod, a_vec.0[2])); simp() using { at(vector_mod, a_vec.0[2]) <= 255u32; } }
     have a_vec.0[2] <= 65521u32 by arithmetic() using { a_vec.0[2] <= 255u32; };
     have at(weighted_b, b_vec.0[3]) <= 255u32;
     apply(uint32_less_equal_to_integer(at(weighted_b, b_vec.0[3]), 255u32)) using { at(weighted_b, b_vec.0[3]) <= 255u32; }
     have to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4;
     have to_integer(b_vec.0[3]) <= 1020 by arithmetic() using { to_integer(b_vec.0[3]) == to_integer(at(weighted_b, b_vec.0[3])) * 4; to_integer(at(weighted_b, b_vec.0[3])) <= 255; };
     have a_vec.0[3] <= 255u32 by { rewrite(a_vec.0[3] == at(vector_mod, a_vec.0[3])); simp() using { at(vector_mod, a_vec.0[3]) <= 255u32; } }
     have a_vec.0[3] <= 65521u32 by arithmetic() using { a_vec.0[3] <= 255u32; };
     step();
     have __rust_checked_43 == 65521u32;
     have __rust_checked_45 <= 255u32 by simp() using { a_vec.0[1] <= 255u32; };
     have __rust_mir_89 == __rust_checked_43 - __rust_checked_45 by simp() using {};
     have __rust_checked_45 <= __rust_checked_43 by { rewrite(__rust_checked_43 == 65521u32); arithmetic() using { __rust_checked_45 <= 255u32; } }
     apply(uint32_subtract_to_integer(__rust_checked_43, __rust_checked_45)) using { __rust_checked_45 <= __rust_checked_43; }
     apply(uint32_to_integer_bounds(__rust_checked_45));
     have to_integer(__rust_mir_89) == to_integer(__rust_checked_43) - to_integer(__rust_checked_45) by { rewrite(__rust_mir_89 == __rust_checked_43 - __rust_checked_45); simp() using { to_integer(__rust_checked_43 - __rust_checked_45) == to_integer(__rust_checked_43) - to_integer(__rust_checked_45); } }
     have to_integer(__rust_checked_43) == 65521 by simp() using { __rust_checked_43 == 65521u32; };
     have to_integer(__rust_mir_89) <= 65521 by { rewrite(to_integer(__rust_mir_89) == to_integer(__rust_checked_43) - to_integer(__rust_checked_45)); rewrite(to_integer(__rust_checked_43) == 65521); arithmetic() using { 0 <= to_integer(__rust_checked_45); } }
     apply(uint32_to_integer_less_equal_implies_less_equal(__rust_mir_89, 65521u32)) using { to_integer(__rust_mir_89) <= 65521; }
     have to_integer(__rust_mir_89) <= 65521 by { apply(uint32_less_equal_to_integer(__rust_mir_89, 65521u32)); simp(); }
     have to_integer(b_vec.0[1]) + to_integer(__rust_mir_89) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[1]) <= 1020; to_integer(__rust_mir_89) <= 65521; };
     apply(uint32_widened_add_guard_by_integer_bound(b_vec.0[1], __rust_mir_89)) using { to_integer(b_vec.0[1]) + to_integer(__rust_mir_89) <= 4294967295; }
     execute_until(assignment(__rust_mir_94, 0));
     have at(weighted_b, b_vec.0[0]) == old((bytes[0] as u32));
     have b_vec.0[0] == old((bytes[0] as u32)) * 4u32 by { rewrite(b_vec.0[0] == at(weighted_b, b_vec.0[0]) * 4u32); simp() using { at(weighted_b, b_vec.0[0]) == old((bytes[0] as u32)); } }
     have at(weighted_b, b_vec.0[1]) == old((bytes[1] as u32));
     have b_vec.0[1] == old((bytes[1] as u32)) * 4u32 by { rewrite(b_vec.0[1] == at(weighted_b, b_vec.0[1]) * 4u32); simp() using { at(weighted_b, b_vec.0[1]) == old((bytes[1] as u32)); } }
     have at(weighted_b, b_vec.0[2]) == old((bytes[2] as u32));
     have b_vec.0[2] == old((bytes[2] as u32)) * 4u32 by { rewrite(b_vec.0[2] == at(weighted_b, b_vec.0[2]) * 4u32); simp() using { at(weighted_b, b_vec.0[2]) == old((bytes[2] as u32)); } }
     have at(weighted_b, b_vec.0[3]) == old((bytes[3] as u32));
     have b_vec.0[3] == old((bytes[3] as u32)) * 4u32 by { rewrite(b_vec.0[3] == at(weighted_b, b_vec.0[3]) * 4u32); simp() using { at(weighted_b, b_vec.0[3]) == old((bytes[3] as u32)); } }
     have __rust_checked_45 == old((bytes[1] as u32)) by simp() using { a_vec.0[1] == old(bytes[1]); };
     have __rust_mir_89 == 65521u32 - old((bytes[1] as u32)) by { rewrite(__rust_mir_89 == __rust_checked_43 - __rust_checked_45); rewrite(__rust_checked_43 == 65521u32); rewrite(__rust_checked_45 == old((bytes[1] as u32))); simp() using {}; }
     mark add_lane_1;
     have at(add_lane_1, b_vec.0[1]) == old((bytes[1] as u32)) * 4u32 by simp() using { b_vec.0[1] == old((bytes[1] as u32)) * 4u32; };
     have at(add_lane_1, __rust_mir_89) == 65521u32 - old((bytes[1] as u32)) by simp() using { __rust_mir_89 == 65521u32 - old((bytes[1] as u32)); };
     have to_integer(at(add_lane_1, b_vec.0[1])) <= 1020 by simp() using { to_integer(b_vec.0[1]) <= 1020; };
     have to_integer(at(add_lane_1, __rust_mir_89)) <= 65521 by simp() using { to_integer(__rust_mir_89) <= 65521; };
     have to_integer(at(add_lane_1, b_vec.0[1])) + to_integer(at(add_lane_1, __rust_mir_89)) <= 4294967295 by arithmetic() using { to_integer(at(add_lane_1, b_vec.0[1])) <= 1020; to_integer(at(add_lane_1, __rust_mir_89)) <= 65521; };
     step();
     have __rust_mir_94 == at(add_lane_1, b_vec.0[1]) + at(add_lane_1, __rust_mir_89);
     apply(uint32_add_to_integer(at(add_lane_1, b_vec.0[1]), at(add_lane_1, __rust_mir_89))) using { to_integer(at(add_lane_1, b_vec.0[1])) + to_integer(at(add_lane_1, __rust_mir_89)) <= 4294967295; }
     have to_integer(__rust_mir_94) == to_integer(at(add_lane_1, b_vec.0[1]) + at(add_lane_1, __rust_mir_89)) by simp() using { __rust_mir_94 == at(add_lane_1, b_vec.0[1]) + at(add_lane_1, __rust_mir_89); };
     have to_integer(__rust_mir_94) <= 66541 by { rewrite(to_integer(__rust_mir_94) == to_integer(at(add_lane_1, b_vec.0[1]) + at(add_lane_1, __rust_mir_89))); rewrite(to_integer(at(add_lane_1, b_vec.0[1]) + at(add_lane_1, __rust_mir_89)) == to_integer(at(add_lane_1, b_vec.0[1])) + to_integer(at(add_lane_1, __rust_mir_89))); arithmetic() using { to_integer(at(add_lane_1, b_vec.0[1])) <= 1020; to_integer(at(add_lane_1, __rust_mir_89)) <= 65521; } }
     have __rust_mir_94 == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))) by { rewrite(__rust_mir_94 == at(add_lane_1, b_vec.0[1]) + at(add_lane_1, __rust_mir_89)); rewrite(at(add_lane_1, b_vec.0[1]) == old((bytes[1] as u32)) * 4u32); rewrite(at(add_lane_1, __rust_mir_89) == 65521u32 - old((bytes[1] as u32))); simp() using {}; }
     mark stored_lane_1;
     have to_integer(at(stored_lane_1, __rust_mir_94)) <= 66541 by simp() using { to_integer(__rust_mir_94) <= 66541; };
     execute_until(assignment(__rust_mir_99, 0));
     have b_vec.0[1] == at(stored_lane_1, __rust_mir_94);
     have to_integer(b_vec.0[1]) <= 66541 by simp() using { to_integer(at(stored_lane_1, __rust_mir_94)) <= 66541; b_vec.0[1] == at(stored_lane_1, __rust_mir_94); };
     have __rust_checked_53 == 65521u32;
     have __rust_checked_54 == old((bytes[2] as u32)) by simp() using { a_vec.0[2] == old(bytes[2]); };
     have __rust_checked_54 <= 255u32 by simp() using { a_vec.0[2] <= 255u32; };
     have __rust_checked_54 < 65521u32 by arithmetic() using { __rust_checked_54 <= 255u32; };
     apply(adler_recombine_difference(__rust_checked_54)) using { __rust_checked_54 < 65521u32; }
     step();
     have __rust_mir_99 == __rust_checked_53 - __rust_checked_54 by simp() using {};
     have __rust_mir_99 == 65521u32 - __rust_checked_54 by { rewrite(__rust_mir_99 == __rust_checked_53 - __rust_checked_54); simp() using { __rust_checked_53 == 65521u32; } }
     execute_until(assignment(__rust_mir_96, 0)); step();
     have __rust_mir_96 == 65521u32 - __rust_checked_54 by simp() using { __rust_mir_99 == 65521u32 - __rust_checked_54; };
     have __rust_mir_96 == 65521u32 - old((bytes[2] as u32)) by { rewrite(__rust_mir_96 == 65521u32 - __rust_checked_54); simp() using { __rust_checked_54 == old((bytes[2] as u32)); } }
     have __rust_mir_96 <= 65521u32 by simp() using { __rust_mir_96 == 65521u32 - __rust_checked_54; 65521u32 - __rust_checked_54 <= 65521u32; };
     apply(uint32_less_equal_to_integer(__rust_mir_96, 65521u32)) using { __rust_mir_96 <= 65521u32; }
     have __rust_mir_96 <= 4294967295u32 / 2u32 by arithmetic() using { __rust_mir_96 <= 65521u32; };
     execute_until(assignment(__rust_mir_100, 0));
     mark multiply_lane_2;
     have at(multiply_lane_2, __rust_mir_96) == 65521u32 - old((bytes[2] as u32)) by simp() using { __rust_mir_96 == 65521u32 - old((bytes[2] as u32)); };
     have to_integer(at(multiply_lane_2, __rust_mir_96)) <= 65521 by simp() using { to_integer(__rust_mir_96) <= 65521; };
     have at(multiply_lane_2, __rust_mir_96) <= 4294967295u32 / 2u32 by simp() using { __rust_mir_96 <= 4294967295u32 / 2u32; };
     have 2u32 == 0u32 or at(multiply_lane_2, __rust_mir_96) <= 4294967295u32 / 2u32 by assumption();
     step();
     have __rust_mir_100 == at(multiply_lane_2, __rust_mir_96) * 2u32;
     apply(uint32_multiply_to_integer(at(multiply_lane_2, __rust_mir_96), 2u32)) using { 2u32 == 0u32 or at(multiply_lane_2, __rust_mir_96) <= 4294967295u32 / 2u32; }
     have to_integer(__rust_mir_100) == to_integer(at(multiply_lane_2, __rust_mir_96) * 2u32) by simp() using { __rust_mir_100 == at(multiply_lane_2, __rust_mir_96) * 2u32; };
     have to_integer(__rust_mir_100) <= 131042 by { rewrite(to_integer(__rust_mir_100) == to_integer(at(multiply_lane_2, __rust_mir_96) * 2u32)); rewrite(to_integer(at(multiply_lane_2, __rust_mir_96) * 2u32) == to_integer(at(multiply_lane_2, __rust_mir_96)) * 2); arithmetic() using { to_integer(at(multiply_lane_2, __rust_mir_96)) <= 65521; } }
     have __rust_mir_100 == (65521u32 - old((bytes[2] as u32))) * 2u32 by { rewrite(__rust_mir_100 == at(multiply_lane_2, __rust_mir_96) * 2u32); rewrite(at(multiply_lane_2, __rust_mir_96) == 65521u32 - old((bytes[2] as u32))); simp() using {}; }
     execute_until(assignment(__rust_mir_95, 0)); step();
     have to_integer(__rust_mir_95) <= 131042 by simp() using { to_integer(__rust_mir_100) <= 131042; };
     have __rust_mir_95 == (65521u32 - old((bytes[2] as u32))) * 2u32 by simp() using { __rust_mir_100 == (65521u32 - old((bytes[2] as u32))) * 2u32; };
     have to_integer(b_vec.0[2]) <= 1020;
     have to_integer(b_vec.0[2]) + to_integer(__rust_mir_95) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[2]) <= 1020; to_integer(__rust_mir_95) <= 131042; };
     apply(uint32_widened_add_guard_by_integer_bound(b_vec.0[2], __rust_mir_95)) using { to_integer(b_vec.0[2]) + to_integer(__rust_mir_95) <= 4294967295; }
     execute_until(assignment(__rust_mir_102, 0));
     mark add_lane_2;
     have at(add_lane_2, b_vec.0[2]) == old((bytes[2] as u32)) * 4u32;
     have at(add_lane_2, __rust_mir_95) == (65521u32 - old((bytes[2] as u32))) * 2u32 by simp() using { __rust_mir_95 == (65521u32 - old((bytes[2] as u32))) * 2u32; };
     have to_integer(at(add_lane_2, b_vec.0[2])) <= 1020 by simp() using { to_integer(b_vec.0[2]) <= 1020; };
     have to_integer(at(add_lane_2, __rust_mir_95)) <= 131042 by simp() using { to_integer(__rust_mir_95) <= 131042; };
     have to_integer(at(add_lane_2, b_vec.0[2])) + to_integer(at(add_lane_2, __rust_mir_95)) <= 4294967295 by arithmetic() using { to_integer(at(add_lane_2, b_vec.0[2])) <= 1020; to_integer(at(add_lane_2, __rust_mir_95)) <= 131042; };
     step();
     have __rust_mir_102 == at(add_lane_2, b_vec.0[2]) + at(add_lane_2, __rust_mir_95);
     apply(uint32_add_to_integer(at(add_lane_2, b_vec.0[2]), at(add_lane_2, __rust_mir_95))) using { to_integer(at(add_lane_2, b_vec.0[2])) + to_integer(at(add_lane_2, __rust_mir_95)) <= 4294967295; }
     have to_integer(__rust_mir_102) == to_integer(at(add_lane_2, b_vec.0[2]) + at(add_lane_2, __rust_mir_95)) by simp() using { __rust_mir_102 == at(add_lane_2, b_vec.0[2]) + at(add_lane_2, __rust_mir_95); };
     have to_integer(__rust_mir_102) <= 132062 by { rewrite(to_integer(__rust_mir_102) == to_integer(at(add_lane_2, b_vec.0[2]) + at(add_lane_2, __rust_mir_95))); rewrite(to_integer(at(add_lane_2, b_vec.0[2]) + at(add_lane_2, __rust_mir_95)) == to_integer(at(add_lane_2, b_vec.0[2])) + to_integer(at(add_lane_2, __rust_mir_95))); arithmetic() using { to_integer(at(add_lane_2, b_vec.0[2])) <= 1020; to_integer(at(add_lane_2, __rust_mir_95)) <= 131042; } }
     have __rust_mir_102 == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32) by { rewrite(__rust_mir_102 == at(add_lane_2, b_vec.0[2]) + at(add_lane_2, __rust_mir_95)); rewrite(at(add_lane_2, b_vec.0[2]) == old((bytes[2] as u32)) * 4u32); rewrite(at(add_lane_2, __rust_mir_95) == (65521u32 - old((bytes[2] as u32))) * 2u32); simp() using {}; }
     mark stored_lane_2;
     have to_integer(at(stored_lane_2, __rust_mir_102)) <= 132062 by simp() using { to_integer(__rust_mir_102) <= 132062; };
     execute_until(assignment(__rust_mir_107, 0));
     have b_vec.0[2] == at(stored_lane_2, __rust_mir_102);
     have to_integer(b_vec.0[2]) <= 132062 by simp() using { to_integer(at(stored_lane_2, __rust_mir_102)) <= 132062; b_vec.0[2] == at(stored_lane_2, __rust_mir_102); };
     have __rust_checked_64 == 65521u32;
     have __rust_checked_65 == old((bytes[3] as u32)) by simp() using { a_vec.0[3] == old(bytes[3]); };
     have __rust_checked_65 <= 255u32 by simp() using { a_vec.0[3] <= 255u32; };
     have __rust_checked_65 < 65521u32 by arithmetic() using { __rust_checked_65 <= 255u32; };
     apply(adler_recombine_difference(__rust_checked_65)) using { __rust_checked_65 < 65521u32; }
     step();
     have __rust_mir_107 == __rust_checked_64 - __rust_checked_65 by simp() using {};
     have __rust_mir_107 == 65521u32 - __rust_checked_65 by { rewrite(__rust_mir_107 == __rust_checked_64 - __rust_checked_65); simp() using { __rust_checked_64 == 65521u32; } }
     execute_until(assignment(__rust_mir_104, 0)); step();
     have __rust_mir_104 == 65521u32 - __rust_checked_65 by simp() using { __rust_mir_107 == 65521u32 - __rust_checked_65; };
     have __rust_mir_104 == 65521u32 - old((bytes[3] as u32)) by { rewrite(__rust_mir_104 == 65521u32 - __rust_checked_65); simp() using { __rust_checked_65 == old((bytes[3] as u32)); } }
     have __rust_mir_104 <= 65521u32 by simp() using { __rust_mir_104 == 65521u32 - __rust_checked_65; 65521u32 - __rust_checked_65 <= 65521u32; };
     apply(uint32_less_equal_to_integer(__rust_mir_104, 65521u32)) using { __rust_mir_104 <= 65521u32; }
     have __rust_mir_104 <= 4294967295u32 / 3u32 by arithmetic() using { __rust_mir_104 <= 65521u32; };
     execute_until(assignment(__rust_mir_108, 0));
     mark multiply_lane_3;
     have at(multiply_lane_3, __rust_mir_104) == 65521u32 - old((bytes[3] as u32)) by simp() using { __rust_mir_104 == 65521u32 - old((bytes[3] as u32)); };
     have to_integer(at(multiply_lane_3, __rust_mir_104)) <= 65521 by simp() using { to_integer(__rust_mir_104) <= 65521; };
     have at(multiply_lane_3, __rust_mir_104) <= 4294967295u32 / 3u32 by simp() using { __rust_mir_104 <= 4294967295u32 / 3u32; };
     have 3u32 == 0u32 or at(multiply_lane_3, __rust_mir_104) <= 4294967295u32 / 3u32 by assumption();
     step();
     have __rust_mir_108 == at(multiply_lane_3, __rust_mir_104) * 3u32;
     apply(uint32_multiply_to_integer(at(multiply_lane_3, __rust_mir_104), 3u32)) using { 3u32 == 0u32 or at(multiply_lane_3, __rust_mir_104) <= 4294967295u32 / 3u32; }
     have to_integer(__rust_mir_108) == to_integer(at(multiply_lane_3, __rust_mir_104) * 3u32) by simp() using { __rust_mir_108 == at(multiply_lane_3, __rust_mir_104) * 3u32; };
     have to_integer(__rust_mir_108) <= 196563 by { rewrite(to_integer(__rust_mir_108) == to_integer(at(multiply_lane_3, __rust_mir_104) * 3u32)); rewrite(to_integer(at(multiply_lane_3, __rust_mir_104) * 3u32) == to_integer(at(multiply_lane_3, __rust_mir_104)) * 3); arithmetic() using { to_integer(at(multiply_lane_3, __rust_mir_104)) <= 65521; } }
     have __rust_mir_108 == (65521u32 - old((bytes[3] as u32))) * 3u32 by { rewrite(__rust_mir_108 == at(multiply_lane_3, __rust_mir_104) * 3u32); rewrite(at(multiply_lane_3, __rust_mir_104) == 65521u32 - old((bytes[3] as u32))); simp() using {}; }
     execute_until(assignment(__rust_mir_103, 0)); step();
     have to_integer(__rust_mir_103) <= 196563 by simp() using { to_integer(__rust_mir_108) <= 196563; };
     have __rust_mir_103 == (65521u32 - old((bytes[3] as u32))) * 3u32 by simp() using { __rust_mir_108 == (65521u32 - old((bytes[3] as u32))) * 3u32; };
     have to_integer(b_vec.0[3]) <= 1020;
     have to_integer(b_vec.0[3]) + to_integer(__rust_mir_103) <= 4294967295 by arithmetic() using { to_integer(b_vec.0[3]) <= 1020; to_integer(__rust_mir_103) <= 196563; };
     apply(uint32_widened_add_guard_by_integer_bound(b_vec.0[3], __rust_mir_103)) using { to_integer(b_vec.0[3]) + to_integer(__rust_mir_103) <= 4294967295; }
     execute_until(assignment(__rust_mir_110, 0));
     mark add_lane_3;
     have at(add_lane_3, b_vec.0[3]) == old((bytes[3] as u32)) * 4u32;
     have at(add_lane_3, __rust_mir_103) == (65521u32 - old((bytes[3] as u32))) * 3u32 by simp() using { __rust_mir_103 == (65521u32 - old((bytes[3] as u32))) * 3u32; };
     have to_integer(at(add_lane_3, b_vec.0[3])) <= 1020 by simp() using { to_integer(b_vec.0[3]) <= 1020; };
     have to_integer(at(add_lane_3, __rust_mir_103)) <= 196563 by simp() using { to_integer(__rust_mir_103) <= 196563; };
     have to_integer(at(add_lane_3, b_vec.0[3])) + to_integer(at(add_lane_3, __rust_mir_103)) <= 4294967295 by arithmetic() using { to_integer(at(add_lane_3, b_vec.0[3])) <= 1020; to_integer(at(add_lane_3, __rust_mir_103)) <= 196563; };
     step();
     have __rust_mir_110 == at(add_lane_3, b_vec.0[3]) + at(add_lane_3, __rust_mir_103);
     apply(uint32_add_to_integer(at(add_lane_3, b_vec.0[3]), at(add_lane_3, __rust_mir_103))) using { to_integer(at(add_lane_3, b_vec.0[3])) + to_integer(at(add_lane_3, __rust_mir_103)) <= 4294967295; }
     have to_integer(__rust_mir_110) == to_integer(at(add_lane_3, b_vec.0[3]) + at(add_lane_3, __rust_mir_103)) by simp() using { __rust_mir_110 == at(add_lane_3, b_vec.0[3]) + at(add_lane_3, __rust_mir_103); };
     have to_integer(__rust_mir_110) <= 197583 by { rewrite(to_integer(__rust_mir_110) == to_integer(at(add_lane_3, b_vec.0[3]) + at(add_lane_3, __rust_mir_103))); rewrite(to_integer(at(add_lane_3, b_vec.0[3]) + at(add_lane_3, __rust_mir_103)) == to_integer(at(add_lane_3, b_vec.0[3])) + to_integer(at(add_lane_3, __rust_mir_103))); arithmetic() using { to_integer(at(add_lane_3, b_vec.0[3])) <= 1020; to_integer(at(add_lane_3, __rust_mir_103)) <= 196563; } }
     have __rust_mir_110 == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32) by { rewrite(__rust_mir_110 == at(add_lane_3, b_vec.0[3]) + at(add_lane_3, __rust_mir_103)); rewrite(at(add_lane_3, b_vec.0[3]) == old((bytes[3] as u32)) * 4u32); rewrite(at(add_lane_3, __rust_mir_103) == (65521u32 - old((bytes[3] as u32))) * 3u32); simp() using {}; }
     mark stored_lane_3;
     have to_integer(at(stored_lane_3, __rust_mir_110)) <= 197583 by simp() using { to_integer(__rust_mir_110) <= 197583; };
     execute_until(assignment(__rust_mir_113, 0));
     have b_vec.0[3] == at(stored_lane_3, __rust_mir_110);
     have to_integer(b_vec.0[3]) <= 197583 by simp() using { to_integer(at(stored_lane_3, __rust_mir_110)) <= 197583; b_vec.0[3] == at(stored_lane_3, __rust_mir_110); };
     have at(stored_lane_1, __rust_mir_94) == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))) by simp() using { __rust_mir_94 == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))); };
     have b_vec.0[1] == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))) by { rewrite(b_vec.0[1] == at(stored_lane_1, __rust_mir_94)); simp() using { at(stored_lane_1, __rust_mir_94) == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))); } }
     have at(stored_lane_2, __rust_mir_102) == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32) by simp() using { __rust_mir_102 == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32); };
     have b_vec.0[2] == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32) by { rewrite(b_vec.0[2] == at(stored_lane_2, __rust_mir_102)); simp() using { at(stored_lane_2, __rust_mir_102) == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32); } }
     have at(stored_lane_3, __rust_mir_110) == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32) by simp() using { __rust_mir_110 == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32); };
     have b_vec.0[3] == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32) by { rewrite(b_vec.0[3] == at(stored_lane_3, __rust_mir_110)); simp() using { at(stored_lane_3, __rust_mir_110) == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32); } }
     have a_vec.0[0] == old((bytes[0] as u32));
     apply(uint32_less_equal_to_integer(a_vec.0[0], 255u32)) using { a_vec.0[0] <= 255u32; }
     have a_vec.0[1] == old((bytes[1] as u32));
     apply(uint32_less_equal_to_integer(a_vec.0[1], 255u32)) using { a_vec.0[1] <= 255u32; }
     have a_vec.0[2] == old((bytes[2] as u32));
     apply(uint32_less_equal_to_integer(a_vec.0[2], 255u32)) using { a_vec.0[2] <= 255u32; }
     have a_vec.0[3] == old((bytes[3] as u32));
     apply(uint32_less_equal_to_integer(a_vec.0[3], 255u32)) using { a_vec.0[3] <= 255u32; }
     execute_until(loop(3));
     have a == 1u32;
     have b == 4u32;
     have to_integer(a) == 1 by simp() using { a == 1u32; };
     have to_integer(a) <= 1 by arithmetic() using { to_integer(a) == 1; };
     mark before_sum_a;
     have at(before_sum_a, ((__rust_mir_115_remaining as u32) as i32)) == 4;
     execute_until(assignment(__rust_mir_121, 0));
     have __rust_mir_115_cursor == at(before_sum_a, __rust_mir_115_cursor) + 1;
     have ((__rust_mir_115_remaining as u32) as i32) == 3;
     have av == a_vec.0[0];
     have av == old((bytes[0] as u32)) by simp() using { av == a_vec.0[0]; a_vec.0[0] == old((bytes[0] as u32)); };
     have to_integer(av) <= 255 by simp() using { av == a_vec.0[0]; to_integer(a_vec.0[0]) <= 255; };
     step();
     have __rust_mir_121 == old((bytes[0] as u32)) by simp() using { av == old((bytes[0] as u32)); };
     have to_integer(__rust_mir_121) <= 255 by simp() using { to_integer(av) <= 255; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by arithmetic() using { to_integer(a) <= 1; to_integer(__rust_mir_121) <= 255; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
     execute_until(assignment(__rust_mir_122, 0));
     mark sum_a_1;
     have at(sum_a_1, a) == 1u32 by simp() using { a == 1u32; };
     have at(sum_a_1, __rust_mir_121) == old((bytes[0] as u32)) by simp() using { __rust_mir_121 == old((bytes[0] as u32)); };
     have to_integer(at(sum_a_1, a)) <= 1 by simp() using { to_integer(a) <= 1; };
     have to_integer(at(sum_a_1, __rust_mir_121)) <= 255 by simp() using { to_integer(__rust_mir_121) <= 255; };
     have to_integer(at(sum_a_1, a)) + to_integer(at(sum_a_1, __rust_mir_121)) <= 4294967295 by arithmetic() using { to_integer(at(sum_a_1, a)) <= 1; to_integer(at(sum_a_1, __rust_mir_121)) <= 255; };
     step();
     have __rust_mir_122 == at(sum_a_1, a) + at(sum_a_1, __rust_mir_121);
     apply(uint32_add_to_integer(at(sum_a_1, a), at(sum_a_1, __rust_mir_121))) using { to_integer(at(sum_a_1, a)) + to_integer(at(sum_a_1, __rust_mir_121)) <= 4294967295; }
     have to_integer(__rust_mir_122) == to_integer(at(sum_a_1, a) + at(sum_a_1, __rust_mir_121)) by simp() using { __rust_mir_122 == at(sum_a_1, a) + at(sum_a_1, __rust_mir_121); };
     have to_integer(__rust_mir_122) <= 256 by { rewrite(to_integer(__rust_mir_122) == to_integer(at(sum_a_1, a) + at(sum_a_1, __rust_mir_121))); rewrite(to_integer(at(sum_a_1, a) + at(sum_a_1, __rust_mir_121)) == to_integer(at(sum_a_1, a)) + to_integer(at(sum_a_1, __rust_mir_121))); arithmetic() using { to_integer(at(sum_a_1, a)) <= 1; to_integer(at(sum_a_1, __rust_mir_121)) <= 255; } }
     have __rust_mir_122 == (1u32 + (old((bytes[0] as u32)))) by { rewrite(__rust_mir_122 == at(sum_a_1, a) + at(sum_a_1, __rust_mir_121)); rewrite(at(sum_a_1, a) == 1u32); rewrite(at(sum_a_1, __rust_mir_121) == old((bytes[0] as u32))); simp() using {}; }
     execute_until(assignment(a, 1)); step();
     have a == (1u32 + (old((bytes[0] as u32)))) by simp() using { __rust_mir_122 == (1u32 + (old((bytes[0] as u32)))); };
     have to_integer(a) <= 256 by simp() using { to_integer(__rust_mir_122) <= 256; };
     // Finish the storage-end and block-exit nodes, then return to the loop head.
     step(); step(); step(); step(); step(); step(); step(); step();
     execute_until(assignment(__rust_mir_121, 0));
     have __rust_mir_115_cursor == at(before_sum_a, __rust_mir_115_cursor) + 2;
     have ((__rust_mir_115_remaining as u32) as i32) == 2;
     have av == a_vec.0[1];
     have av == old((bytes[1] as u32)) by simp() using { av == a_vec.0[1]; a_vec.0[1] == old((bytes[1] as u32)); };
     have to_integer(av) <= 255 by simp() using { av == a_vec.0[1]; to_integer(a_vec.0[1]) <= 255; };
     step();
     have __rust_mir_121 == old((bytes[1] as u32)) by simp() using { av == old((bytes[1] as u32)); };
     have to_integer(__rust_mir_121) <= 255 by simp() using { to_integer(av) <= 255; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by arithmetic() using { to_integer(a) <= 256; to_integer(__rust_mir_121) <= 255; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
     execute_until(assignment(__rust_mir_122, 0));
     mark sum_a_2;
     have at(sum_a_2, a) == (1u32 + (old((bytes[0] as u32)))) by simp() using { a == (1u32 + (old((bytes[0] as u32)))); };
     have at(sum_a_2, __rust_mir_121) == old((bytes[1] as u32)) by simp() using { __rust_mir_121 == old((bytes[1] as u32)); };
     have to_integer(at(sum_a_2, a)) <= 256 by simp() using { to_integer(a) <= 256; };
     have to_integer(at(sum_a_2, __rust_mir_121)) <= 255 by simp() using { to_integer(__rust_mir_121) <= 255; };
     have to_integer(at(sum_a_2, a)) + to_integer(at(sum_a_2, __rust_mir_121)) <= 4294967295 by arithmetic() using { to_integer(at(sum_a_2, a)) <= 256; to_integer(at(sum_a_2, __rust_mir_121)) <= 255; };
     step();
     have __rust_mir_122 == at(sum_a_2, a) + at(sum_a_2, __rust_mir_121);
     apply(uint32_add_to_integer(at(sum_a_2, a), at(sum_a_2, __rust_mir_121))) using { to_integer(at(sum_a_2, a)) + to_integer(at(sum_a_2, __rust_mir_121)) <= 4294967295; }
     have to_integer(__rust_mir_122) == to_integer(at(sum_a_2, a) + at(sum_a_2, __rust_mir_121)) by simp() using { __rust_mir_122 == at(sum_a_2, a) + at(sum_a_2, __rust_mir_121); };
     have to_integer(__rust_mir_122) <= 511 by { rewrite(to_integer(__rust_mir_122) == to_integer(at(sum_a_2, a) + at(sum_a_2, __rust_mir_121))); rewrite(to_integer(at(sum_a_2, a) + at(sum_a_2, __rust_mir_121)) == to_integer(at(sum_a_2, a)) + to_integer(at(sum_a_2, __rust_mir_121))); arithmetic() using { to_integer(at(sum_a_2, a)) <= 256; to_integer(at(sum_a_2, __rust_mir_121)) <= 255; } }
     have __rust_mir_122 == ((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) by { rewrite(__rust_mir_122 == at(sum_a_2, a) + at(sum_a_2, __rust_mir_121)); rewrite(at(sum_a_2, a) == (1u32 + (old((bytes[0] as u32))))); rewrite(at(sum_a_2, __rust_mir_121) == old((bytes[1] as u32))); simp() using {}; }
     execute_until(assignment(a, 1)); step();
     have a == ((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) by simp() using { __rust_mir_122 == ((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))); };
     have to_integer(a) <= 511 by simp() using { to_integer(__rust_mir_122) <= 511; };
     // Finish the storage-end and block-exit nodes, then return to the loop head.
     step(); step(); step(); step(); step(); step(); step(); step();
     execute_until(assignment(__rust_mir_121, 0));
     have __rust_mir_115_cursor == at(before_sum_a, __rust_mir_115_cursor) + 3;
     have ((__rust_mir_115_remaining as u32) as i32) == 1;
     have av == a_vec.0[2];
     have av == old((bytes[2] as u32)) by simp() using { av == a_vec.0[2]; a_vec.0[2] == old((bytes[2] as u32)); };
     have to_integer(av) <= 255 by simp() using { av == a_vec.0[2]; to_integer(a_vec.0[2]) <= 255; };
     step();
     have __rust_mir_121 == old((bytes[2] as u32)) by simp() using { av == old((bytes[2] as u32)); };
     have to_integer(__rust_mir_121) <= 255 by simp() using { to_integer(av) <= 255; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by arithmetic() using { to_integer(a) <= 511; to_integer(__rust_mir_121) <= 255; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
     execute_until(assignment(__rust_mir_122, 0));
     mark sum_a_3;
     have at(sum_a_3, a) == ((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) by simp() using { a == ((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))); };
     have at(sum_a_3, __rust_mir_121) == old((bytes[2] as u32)) by simp() using { __rust_mir_121 == old((bytes[2] as u32)); };
     have to_integer(at(sum_a_3, a)) <= 511 by simp() using { to_integer(a) <= 511; };
     have to_integer(at(sum_a_3, __rust_mir_121)) <= 255 by simp() using { to_integer(__rust_mir_121) <= 255; };
     have to_integer(at(sum_a_3, a)) + to_integer(at(sum_a_3, __rust_mir_121)) <= 4294967295 by arithmetic() using { to_integer(at(sum_a_3, a)) <= 511; to_integer(at(sum_a_3, __rust_mir_121)) <= 255; };
     step();
     have __rust_mir_122 == at(sum_a_3, a) + at(sum_a_3, __rust_mir_121);
     apply(uint32_add_to_integer(at(sum_a_3, a), at(sum_a_3, __rust_mir_121))) using { to_integer(at(sum_a_3, a)) + to_integer(at(sum_a_3, __rust_mir_121)) <= 4294967295; }
     have to_integer(__rust_mir_122) == to_integer(at(sum_a_3, a) + at(sum_a_3, __rust_mir_121)) by simp() using { __rust_mir_122 == at(sum_a_3, a) + at(sum_a_3, __rust_mir_121); };
     have to_integer(__rust_mir_122) <= 766 by { rewrite(to_integer(__rust_mir_122) == to_integer(at(sum_a_3, a) + at(sum_a_3, __rust_mir_121))); rewrite(to_integer(at(sum_a_3, a) + at(sum_a_3, __rust_mir_121)) == to_integer(at(sum_a_3, a)) + to_integer(at(sum_a_3, __rust_mir_121))); arithmetic() using { to_integer(at(sum_a_3, a)) <= 511; to_integer(at(sum_a_3, __rust_mir_121)) <= 255; } }
     have __rust_mir_122 == (((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) by { rewrite(__rust_mir_122 == at(sum_a_3, a) + at(sum_a_3, __rust_mir_121)); rewrite(at(sum_a_3, a) == ((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32))))); rewrite(at(sum_a_3, __rust_mir_121) == old((bytes[2] as u32))); simp() using {}; }
     execute_until(assignment(a, 1)); step();
     have a == (((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) by simp() using { __rust_mir_122 == (((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))); };
     have to_integer(a) <= 766 by simp() using { to_integer(__rust_mir_122) <= 766; };
     // Finish the storage-end and block-exit nodes, then return to the loop head.
     step(); step(); step(); step(); step(); step(); step(); step();
     execute_until(assignment(__rust_mir_121, 0));
     have __rust_mir_115_cursor == at(before_sum_a, __rust_mir_115_cursor) + 4;
     have ((__rust_mir_115_remaining as u32) as i32) == 0;
     have av == a_vec.0[3];
     have av == old((bytes[3] as u32)) by simp() using { av == a_vec.0[3]; a_vec.0[3] == old((bytes[3] as u32)); };
     have to_integer(av) <= 255 by simp() using { av == a_vec.0[3]; to_integer(a_vec.0[3]) <= 255; };
     step();
     have __rust_mir_121 == old((bytes[3] as u32)) by simp() using { av == old((bytes[3] as u32)); };
     have to_integer(__rust_mir_121) <= 255 by simp() using { to_integer(av) <= 255; };
     have to_integer(a) + to_integer(__rust_mir_121) <= 4294967295 by arithmetic() using { to_integer(a) <= 766; to_integer(__rust_mir_121) <= 255; };
     apply(uint32_widened_add_guard_by_integer_bound(a, __rust_mir_121)) using { to_integer(a) + to_integer(__rust_mir_121) <= 4294967295; }
     execute_until(assignment(__rust_mir_122, 0));
     mark sum_a_4;
     have at(sum_a_4, a) == (((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) by simp() using { a == (((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))); };
     have at(sum_a_4, __rust_mir_121) == old((bytes[3] as u32)) by simp() using { __rust_mir_121 == old((bytes[3] as u32)); };
     have to_integer(at(sum_a_4, a)) <= 766 by simp() using { to_integer(a) <= 766; };
     have to_integer(at(sum_a_4, __rust_mir_121)) <= 255 by simp() using { to_integer(__rust_mir_121) <= 255; };
     have to_integer(at(sum_a_4, a)) + to_integer(at(sum_a_4, __rust_mir_121)) <= 4294967295 by arithmetic() using { to_integer(at(sum_a_4, a)) <= 766; to_integer(at(sum_a_4, __rust_mir_121)) <= 255; };
     step();
     have __rust_mir_122 == at(sum_a_4, a) + at(sum_a_4, __rust_mir_121);
     apply(uint32_add_to_integer(at(sum_a_4, a), at(sum_a_4, __rust_mir_121))) using { to_integer(at(sum_a_4, a)) + to_integer(at(sum_a_4, __rust_mir_121)) <= 4294967295; }
     have to_integer(__rust_mir_122) == to_integer(at(sum_a_4, a) + at(sum_a_4, __rust_mir_121)) by simp() using { __rust_mir_122 == at(sum_a_4, a) + at(sum_a_4, __rust_mir_121); };
     have to_integer(__rust_mir_122) <= 1021 by { rewrite(to_integer(__rust_mir_122) == to_integer(at(sum_a_4, a) + at(sum_a_4, __rust_mir_121))); rewrite(to_integer(at(sum_a_4, a) + at(sum_a_4, __rust_mir_121)) == to_integer(at(sum_a_4, a)) + to_integer(at(sum_a_4, __rust_mir_121))); arithmetic() using { to_integer(at(sum_a_4, a)) <= 766; to_integer(at(sum_a_4, __rust_mir_121)) <= 255; } }
     have __rust_mir_122 == ((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32)))) by { rewrite(__rust_mir_122 == at(sum_a_4, a) + at(sum_a_4, __rust_mir_121)); rewrite(at(sum_a_4, a) == (((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32))))); rewrite(at(sum_a_4, __rust_mir_121) == old((bytes[3] as u32))); simp() using {}; }
     execute_until(assignment(a, 1)); step();
     have a == ((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32)))) by simp() using { __rust_mir_122 == ((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32)))); };
     have to_integer(a) <= 1021 by simp() using { to_integer(__rust_mir_122) <= 1021; };
     // Finish the storage-end and block-exit nodes, then return to the loop head.
     step(); step(); step(); step(); step(); step(); step(); step();
     have ((__rust_mir_115_remaining as u32) as i32) == 0;
     execute_until(loop(4));
     have b == 4u32;
     have to_integer(b) == 4 by simp() using { b == 4u32; };
     have to_integer(b) <= 4 by arithmetic() using { to_integer(b) == 4; };
     mark before_sum_b;
     have at(before_sum_b, ((__rust_mir_127_remaining as u32) as i32)) == 4;
     execute_until(assignment(__rust_mir_133, 0));
     have __rust_mir_127_cursor == at(before_sum_b, __rust_mir_127_cursor) + 1;
     have ((__rust_mir_127_remaining as u32) as i32) == 3;
     have bv == b_vec.0[0];
     have bv == old((bytes[0] as u32)) * 4u32 by simp() using { bv == b_vec.0[0]; b_vec.0[0] == old((bytes[0] as u32)) * 4u32; };
     have to_integer(bv) <= 1020 by simp() using { bv == b_vec.0[0]; to_integer(b_vec.0[0]) <= 1020; };
     step();
     have __rust_mir_133 == old((bytes[0] as u32)) * 4u32 by simp() using { bv == old((bytes[0] as u32)) * 4u32; };
     have to_integer(__rust_mir_133) <= 1020 by simp() using { to_integer(bv) <= 1020; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by arithmetic() using { to_integer(b) <= 4; to_integer(__rust_mir_133) <= 1020; };
     apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
     execute_until(assignment(__rust_mir_134, 0));
     mark sum_b_1;
     have at(sum_b_1, b) == 4u32 by simp() using { b == 4u32; };
     have at(sum_b_1, __rust_mir_133) == old((bytes[0] as u32)) * 4u32 by simp() using { __rust_mir_133 == old((bytes[0] as u32)) * 4u32; };
     have to_integer(at(sum_b_1, b)) <= 4 by simp() using { to_integer(b) <= 4; };
     have to_integer(at(sum_b_1, __rust_mir_133)) <= 1020 by simp() using { to_integer(__rust_mir_133) <= 1020; };
     have to_integer(at(sum_b_1, b)) + to_integer(at(sum_b_1, __rust_mir_133)) <= 4294967295 by arithmetic() using { to_integer(at(sum_b_1, b)) <= 4; to_integer(at(sum_b_1, __rust_mir_133)) <= 1020; };
     step();
     have __rust_mir_134 == at(sum_b_1, b) + at(sum_b_1, __rust_mir_133);
     apply(uint32_add_to_integer(at(sum_b_1, b), at(sum_b_1, __rust_mir_133))) using { to_integer(at(sum_b_1, b)) + to_integer(at(sum_b_1, __rust_mir_133)) <= 4294967295; }
     have to_integer(__rust_mir_134) == to_integer(at(sum_b_1, b) + at(sum_b_1, __rust_mir_133)) by simp() using { __rust_mir_134 == at(sum_b_1, b) + at(sum_b_1, __rust_mir_133); };
     have to_integer(__rust_mir_134) <= 1024 by { rewrite(to_integer(__rust_mir_134) == to_integer(at(sum_b_1, b) + at(sum_b_1, __rust_mir_133))); rewrite(to_integer(at(sum_b_1, b) + at(sum_b_1, __rust_mir_133)) == to_integer(at(sum_b_1, b)) + to_integer(at(sum_b_1, __rust_mir_133))); arithmetic() using { to_integer(at(sum_b_1, b)) <= 4; to_integer(at(sum_b_1, __rust_mir_133)) <= 1020; } }
     have __rust_mir_134 == (4u32 + (old((bytes[0] as u32)) * 4u32)) by { rewrite(__rust_mir_134 == at(sum_b_1, b) + at(sum_b_1, __rust_mir_133)); rewrite(at(sum_b_1, b) == 4u32); rewrite(at(sum_b_1, __rust_mir_133) == old((bytes[0] as u32)) * 4u32); simp() using {}; }
     execute_until(assignment(b, 5)); step();
     have b == (4u32 + (old((bytes[0] as u32)) * 4u32)) by simp() using { __rust_mir_134 == (4u32 + (old((bytes[0] as u32)) * 4u32)); };
     have to_integer(b) <= 1024 by simp() using { to_integer(__rust_mir_134) <= 1024; };
     // Finish the storage-end and block-exit nodes, then return to the loop head.
     step(); step(); step(); step(); step(); step(); step(); step();
     execute_until(assignment(__rust_mir_133, 0));
     have __rust_mir_127_cursor == at(before_sum_b, __rust_mir_127_cursor) + 2;
     have ((__rust_mir_127_remaining as u32) as i32) == 2;
     have bv == b_vec.0[1];
     have bv == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))) by simp() using { bv == b_vec.0[1]; b_vec.0[1] == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))); };
     have to_integer(bv) <= 66541 by simp() using { bv == b_vec.0[1]; to_integer(b_vec.0[1]) <= 66541; };
     step();
     have __rust_mir_133 == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))) by simp() using { bv == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))); };
     have to_integer(__rust_mir_133) <= 66541 by simp() using { to_integer(bv) <= 66541; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by arithmetic() using { to_integer(b) <= 1024; to_integer(__rust_mir_133) <= 66541; };
     apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
     execute_until(assignment(__rust_mir_134, 0));
     mark sum_b_2;
     have at(sum_b_2, b) == (4u32 + (old((bytes[0] as u32)) * 4u32)) by simp() using { b == (4u32 + (old((bytes[0] as u32)) * 4u32)); };
     have at(sum_b_2, __rust_mir_133) == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))) by simp() using { __rust_mir_133 == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))); };
     have to_integer(at(sum_b_2, b)) <= 1024 by simp() using { to_integer(b) <= 1024; };
     have to_integer(at(sum_b_2, __rust_mir_133)) <= 66541 by simp() using { to_integer(__rust_mir_133) <= 66541; };
     have to_integer(at(sum_b_2, b)) + to_integer(at(sum_b_2, __rust_mir_133)) <= 4294967295 by arithmetic() using { to_integer(at(sum_b_2, b)) <= 1024; to_integer(at(sum_b_2, __rust_mir_133)) <= 66541; };
     step();
     have __rust_mir_134 == at(sum_b_2, b) + at(sum_b_2, __rust_mir_133);
     apply(uint32_add_to_integer(at(sum_b_2, b), at(sum_b_2, __rust_mir_133))) using { to_integer(at(sum_b_2, b)) + to_integer(at(sum_b_2, __rust_mir_133)) <= 4294967295; }
     have to_integer(__rust_mir_134) == to_integer(at(sum_b_2, b) + at(sum_b_2, __rust_mir_133)) by simp() using { __rust_mir_134 == at(sum_b_2, b) + at(sum_b_2, __rust_mir_133); };
     have to_integer(__rust_mir_134) <= 67565 by { rewrite(to_integer(__rust_mir_134) == to_integer(at(sum_b_2, b) + at(sum_b_2, __rust_mir_133))); rewrite(to_integer(at(sum_b_2, b) + at(sum_b_2, __rust_mir_133)) == to_integer(at(sum_b_2, b)) + to_integer(at(sum_b_2, __rust_mir_133))); arithmetic() using { to_integer(at(sum_b_2, b)) <= 1024; to_integer(at(sum_b_2, __rust_mir_133)) <= 66541; } }
     have __rust_mir_134 == ((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) by { rewrite(__rust_mir_134 == at(sum_b_2, b) + at(sum_b_2, __rust_mir_133)); rewrite(at(sum_b_2, b) == (4u32 + (old((bytes[0] as u32)) * 4u32))); rewrite(at(sum_b_2, __rust_mir_133) == old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32)))); simp() using {}; }
     execute_until(assignment(b, 5)); step();
     have b == ((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) by simp() using { __rust_mir_134 == ((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))); };
     have to_integer(b) <= 67565 by simp() using { to_integer(__rust_mir_134) <= 67565; };
     // Finish the storage-end and block-exit nodes, then return to the loop head.
     step(); step(); step(); step(); step(); step(); step(); step();
     execute_until(assignment(__rust_mir_133, 0));
     have __rust_mir_127_cursor == at(before_sum_b, __rust_mir_127_cursor) + 3;
     have ((__rust_mir_127_remaining as u32) as i32) == 1;
     have bv == b_vec.0[2];
     have bv == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32) by simp() using { bv == b_vec.0[2]; b_vec.0[2] == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32); };
     have to_integer(bv) <= 132062 by simp() using { bv == b_vec.0[2]; to_integer(b_vec.0[2]) <= 132062; };
     step();
     have __rust_mir_133 == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32) by simp() using { bv == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32); };
     have to_integer(__rust_mir_133) <= 132062 by simp() using { to_integer(bv) <= 132062; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by arithmetic() using { to_integer(b) <= 67565; to_integer(__rust_mir_133) <= 132062; };
     apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
     execute_until(assignment(__rust_mir_134, 0));
     mark sum_b_3;
     have at(sum_b_3, b) == ((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) by simp() using { b == ((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))); };
     have at(sum_b_3, __rust_mir_133) == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32) by simp() using { __rust_mir_133 == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32); };
     have to_integer(at(sum_b_3, b)) <= 67565 by simp() using { to_integer(b) <= 67565; };
     have to_integer(at(sum_b_3, __rust_mir_133)) <= 132062 by simp() using { to_integer(__rust_mir_133) <= 132062; };
     have to_integer(at(sum_b_3, b)) + to_integer(at(sum_b_3, __rust_mir_133)) <= 4294967295 by arithmetic() using { to_integer(at(sum_b_3, b)) <= 67565; to_integer(at(sum_b_3, __rust_mir_133)) <= 132062; };
     step();
     have __rust_mir_134 == at(sum_b_3, b) + at(sum_b_3, __rust_mir_133);
     apply(uint32_add_to_integer(at(sum_b_3, b), at(sum_b_3, __rust_mir_133))) using { to_integer(at(sum_b_3, b)) + to_integer(at(sum_b_3, __rust_mir_133)) <= 4294967295; }
     have to_integer(__rust_mir_134) == to_integer(at(sum_b_3, b) + at(sum_b_3, __rust_mir_133)) by simp() using { __rust_mir_134 == at(sum_b_3, b) + at(sum_b_3, __rust_mir_133); };
     have to_integer(__rust_mir_134) <= 199627 by { rewrite(to_integer(__rust_mir_134) == to_integer(at(sum_b_3, b) + at(sum_b_3, __rust_mir_133))); rewrite(to_integer(at(sum_b_3, b) + at(sum_b_3, __rust_mir_133)) == to_integer(at(sum_b_3, b)) + to_integer(at(sum_b_3, __rust_mir_133))); arithmetic() using { to_integer(at(sum_b_3, b)) <= 67565; to_integer(at(sum_b_3, __rust_mir_133)) <= 132062; } }
     have __rust_mir_134 == (((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) by { rewrite(__rust_mir_134 == at(sum_b_3, b) + at(sum_b_3, __rust_mir_133)); rewrite(at(sum_b_3, b) == ((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32)))))); rewrite(at(sum_b_3, __rust_mir_133) == old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32)); simp() using {}; }
     execute_until(assignment(b, 5)); step();
     have b == (((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) by simp() using { __rust_mir_134 == (((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))); };
     have to_integer(b) <= 199627 by simp() using { to_integer(__rust_mir_134) <= 199627; };
     // Finish the storage-end and block-exit nodes, then return to the loop head.
     step(); step(); step(); step(); step(); step(); step(); step();
     execute_until(assignment(__rust_mir_133, 0));
     have __rust_mir_127_cursor == at(before_sum_b, __rust_mir_127_cursor) + 4;
     have ((__rust_mir_127_remaining as u32) as i32) == 0;
     have bv == b_vec.0[3];
     have bv == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32) by simp() using { bv == b_vec.0[3]; b_vec.0[3] == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32); };
     have to_integer(bv) <= 197583 by simp() using { bv == b_vec.0[3]; to_integer(b_vec.0[3]) <= 197583; };
     step();
     have __rust_mir_133 == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32) by simp() using { bv == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32); };
     have to_integer(__rust_mir_133) <= 197583 by simp() using { to_integer(bv) <= 197583; };
     have to_integer(b) + to_integer(__rust_mir_133) <= 4294967295 by arithmetic() using { to_integer(b) <= 199627; to_integer(__rust_mir_133) <= 197583; };
     apply(uint32_widened_add_guard_by_integer_bound(b, __rust_mir_133)) using { to_integer(b) + to_integer(__rust_mir_133) <= 4294967295; }
     execute_until(assignment(__rust_mir_134, 0));
     mark sum_b_4;
     have at(sum_b_4, b) == (((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) by simp() using { b == (((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))); };
     have at(sum_b_4, __rust_mir_133) == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32) by simp() using { __rust_mir_133 == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32); };
     have to_integer(at(sum_b_4, b)) <= 199627 by simp() using { to_integer(b) <= 199627; };
     have to_integer(at(sum_b_4, __rust_mir_133)) <= 197583 by simp() using { to_integer(__rust_mir_133) <= 197583; };
     have to_integer(at(sum_b_4, b)) + to_integer(at(sum_b_4, __rust_mir_133)) <= 4294967295 by arithmetic() using { to_integer(at(sum_b_4, b)) <= 199627; to_integer(at(sum_b_4, __rust_mir_133)) <= 197583; };
     step();
     have __rust_mir_134 == at(sum_b_4, b) + at(sum_b_4, __rust_mir_133);
     apply(uint32_add_to_integer(at(sum_b_4, b), at(sum_b_4, __rust_mir_133))) using { to_integer(at(sum_b_4, b)) + to_integer(at(sum_b_4, __rust_mir_133)) <= 4294967295; }
     have to_integer(__rust_mir_134) == to_integer(at(sum_b_4, b) + at(sum_b_4, __rust_mir_133)) by simp() using { __rust_mir_134 == at(sum_b_4, b) + at(sum_b_4, __rust_mir_133); };
     have to_integer(__rust_mir_134) <= 397210 by { rewrite(to_integer(__rust_mir_134) == to_integer(at(sum_b_4, b) + at(sum_b_4, __rust_mir_133))); rewrite(to_integer(at(sum_b_4, b) + at(sum_b_4, __rust_mir_133)) == to_integer(at(sum_b_4, b)) + to_integer(at(sum_b_4, __rust_mir_133))); arithmetic() using { to_integer(at(sum_b_4, b)) <= 199627; to_integer(at(sum_b_4, __rust_mir_133)) <= 197583; } }
     have __rust_mir_134 == ((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32))) by { rewrite(__rust_mir_134 == at(sum_b_4, b) + at(sum_b_4, __rust_mir_133)); rewrite(at(sum_b_4, b) == (((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32)))); rewrite(at(sum_b_4, __rust_mir_133) == old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)); simp() using {}; }
     execute_until(assignment(b, 5)); step();
     have b == ((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32))) by simp() using { __rust_mir_134 == ((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32))); };
     have to_integer(b) <= 397210 by simp() using { to_integer(__rust_mir_134) <= 397210; };
     // Finish the storage-end and block-exit nodes, then return to the loop head.
     step(); step(); step(); step(); step(); step(); step(); step();
     have ((__rust_mir_127_remaining as u32) as i32) == 0;
     execute_until(loop(5));
     have remainder_len == 0u64;
     execute_until(assignment(__rust_mir_149, 0));
     mark output_a;
     step();
     have at(output_a, __rust_checked_32) == ((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32)))) by simp() using { a == ((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32)))); };
     have at(output_a, __rust_checked_34) == 65521u32;
     have __rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34) by simp() using {};
     have __rust_mir_149 == (((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32 by { rewrite(__rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34)); rewrite(at(output_a, __rust_checked_32) == ((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))); rewrite(at(output_a, __rust_checked_34) == 65521u32); simp() using {}; }
     apply(uint32_remainder_less_than_divisor(at(output_a, __rust_checked_32), 65521u32));
     have __rust_mir_149 < 65521u32 by simp() using { __rust_mir_149 == at(output_a, __rust_checked_32) % at(output_a, __rust_checked_34); at(output_a, __rust_checked_34) == 65521u32; at(output_a, __rust_checked_32) % 65521u32 < 65521u32; };
     apply(uint32_to_integer_bounds(__rust_mir_149));
     apply(uint32_less_than_to_integer(__rust_mir_149, 65521u32)) using { __rust_mir_149 < 65521u32; }
     have to_integer(__rust_mir_149) <= 65535 by arithmetic() using { to_integer(__rust_mir_149) < 65521; };
     mark reduced_a;
     execute_until(assignment(__rust_mir_151, 0));
     mark output_b;
     step();
     have at(output_b, __rust_checked_35) == ((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32))) by simp() using { b == ((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32))); };
     have at(output_b, __rust_checked_37) == 65521u32;
     have __rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37) by simp() using {};
     have __rust_mir_151 == (((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32 by { rewrite(__rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37)); rewrite(at(output_b, __rust_checked_35) == ((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))); rewrite(at(output_b, __rust_checked_37) == 65521u32); simp() using {}; }
     apply(uint32_remainder_less_than_divisor(at(output_b, __rust_checked_35), 65521u32));
     have __rust_mir_151 < 65521u32 by simp() using { __rust_mir_151 == at(output_b, __rust_checked_35) % at(output_b, __rust_checked_37); at(output_b, __rust_checked_37) == 65521u32; at(output_b, __rust_checked_35) % 65521u32 < 65521u32; };
     apply(uint32_to_integer_bounds(__rust_mir_151));
     apply(uint32_less_than_to_integer(__rust_mir_151, 65521u32)) using { __rust_mir_151 < 65521u32; }
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
     have bytes[2] == old(bytes[2]) by simp() using {};
     have bytes[3] == old(bytes[3]) by simp() using {};
     have to_integer(self.a) == to_integer((((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32) by {
      rewrite(to_integer(self.a) == to_integer(at(reduced_a, __rust_mir_149)));
      rewrite(at(reduced_a, __rust_mir_149) == (((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32); normalize();
     }
     have to_integer((((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32) == old(adler_spec_a(bytes, 4, 1)) by assumption();
     have to_integer(self.a) == old(adler_spec_a(bytes, 4, 1)) by {
      rewrite(to_integer(self.a) == to_integer((((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32)); assumption();
     }
     have to_integer(self.b) == to_integer((((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32) by {
      rewrite(to_integer(self.b) == to_integer(at(reduced_b, __rust_mir_151)));
      rewrite(at(reduced_b, __rust_mir_151) == (((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32); normalize();
     }
     have to_integer((((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32) == old(adler_spec_b(bytes, 4, 1, 0)) by assumption();
     have to_integer(self.b) == old(adler_spec_b(bytes, 4, 1, 0)) by {
      rewrite(to_integer(self.b) == to_integer((((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32)); assumption();
     }
     simp() using { to_integer(self.a) == old(adler_spec_a(bytes, 4, 1)); to_integer(self.b) == old(adler_spec_b(bytes, 4, 1, 0)); bytes[0] == old(bytes[0]); bytes[1] == old(bytes[1]); bytes[2] == old(bytes[2]); bytes[3] == old(bytes[3]); to_integer(self.a) == to_integer(at(reduced_a, __rust_mir_149)); at(reduced_a, __rust_mir_149) == (((((1u32 + (old((bytes[0] as u32)))) + (old((bytes[1] as u32)))) + (old((bytes[2] as u32)))) + (old((bytes[3] as u32))))) % 65521u32; to_integer(self.b) == to_integer(at(reduced_b, __rust_mir_151)); at(reduced_b, __rust_mir_151) == (((((4u32 + (old((bytes[0] as u32)) * 4u32)) + (old((bytes[1] as u32)) * 4u32 + (65521u32 - old((bytes[1] as u32))))) + (old((bytes[2] as u32)) * 4u32 + ((65521u32 - old((bytes[2] as u32))) * 2u32))) + (old((bytes[3] as u32)) * 4u32 + ((65521u32 - old((bytes[3] as u32))) * 3u32)))) % 65521u32; }
    }
}
