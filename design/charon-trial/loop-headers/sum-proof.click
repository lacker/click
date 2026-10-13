verifying "sum.rs";
function prefix(bytes: const uint8*, end: uint64) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer((int32)bytes[k])
    })
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures to_integer(result) == old(prefix(bytes, bytes.len()));
} by {
    execute_until(loop(0));
    have prefix(bytes, i) == 0 by {
        peel(prefix(bytes, i)) using {
            i <= 0u64;
        } simp();
    }
    loop {
        decreases bytes.len() - i;
        views bytes[0..bytes.len()];
        invariant i <= bytes.len();
        invariant bytes.len() <= 1000u64;
        invariant 0 <= to_integer(total) and to_integer(total) <= 255 * to_integer(i);
        invariant to_integer(total) == prefix(bytes, i);
        preserve by {
            execute_until(read(0)); step();
            have defined(bytes[i]) by {
                transport(at(function.entry, viewable(bytes[0..bytes.len()])), defined(bytes[i])) using {
                    at(function.entry, viewable(bytes[0..bytes.len()]));
                    i < bytes.len();
                    bytes.len() <= 9223372036854775807u64;
                }
            }
            have 0 <= (int32)bytes[i] and 255 >= (int32)bytes[i];
            have 0 <= to_integer(total);
            have defined(total + (int32)bytes[i]) by auto;
            have i < 18446744073709551615u64 by auto;
            have prefix(bytes, i + 1u64) == prefix(bytes, i) + to_integer((int32)bytes[i]) by {
                peel(prefix(bytes, i + 1u64)) using {
                    0u64 <= i;
                    i < 18446744073709551615u64;
                }
                simp();
            }
            have to_integer(total + (int32)bytes[i]) == prefix(bytes, i + 1u64) by auto;
            have 0 <= to_integer(total + (int32)bytes[i]) by auto;
            have to_integer(total + (int32)bytes[i]) <= 255 * to_integer(i + 1u64) by auto;
            execute_until(assignment(i, 1));
            step();
            have i <= bytes.len();
            step(); step(); step();
            close_invariants();
        }
    }
    have i == bytes.len() by {
        apply(uint64_less_equal_and_not_less_than_implies_equal(i, bytes.len())) using {
            i <= bytes.len();
            not i < bytes.len();
        }
    }
    have prefix(bytes, i) == prefix(bytes, bytes.len()) by {
        rewrite(i == bytes.len());
        simp();
    }
    have to_integer(total) == prefix(bytes, bytes.len()) by auto;
    execute();
    simp();
}
