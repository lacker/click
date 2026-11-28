import click::integer;
verifying "enumerate.rs";

// `for (i, x) in xs.iter().enumerate()` is `core`'s `Enumerate { iter,
// count }`: each iteration yields index `iter.count` and the element at
// `iter.as_slice()`, then counts it and moves the slice on.

fn last_index(bytes: &[u8]) -> usize {
    views bytes[0..bytes.len()];
    ensures bytes.len() != 0u64 implies result == bytes.len() - 1u64;
} by {
    step_until(loop(0).entry);
    loop {
        decreases iter.len();
        views bytes[0..bytes.len()];
        invariant iter.len() <= bytes.len();
        invariant iter.count == bytes.len() - iter.len();
        invariant iter.as_slice().as_ptr() == bytes.as_ptr() + iter.count;
        invariant iter.count != 0u64 implies last == iter.count - 1u64;
        maintain by {
            if 0u64 < iter.len() {
                mark taken;
                have to_integer(iter.count) < to_integer(bytes.len());
                have to_integer(iter.count) + 1 <= to_integer(bytes.len());
                have to_integer(iter.count) + 1 <= 18446744073709551615;
                apply(integer::uint64_add_to_integer(iter.count, 1u64));
                have to_integer(iter.count + 1u64) <= to_integer(bytes.len()) by {
                    rewrite(to_integer(iter.count + 1u64), to_integer(iter.count) + 1);
                    close();
                }
                have (bytes.as_ptr() + iter.count) + 1u64 == bytes.as_ptr() + (iter.count + 1u64);
                step_until(loop.back_edge);
                have iter.count == at(taken, iter.count) + 1u64;
                have iter.len() == at(taken, iter.len()) - 1u64;
                have iter.as_slice().as_ptr() == bytes.as_ptr() + iter.count;
                have last == iter.count - 1u64;
                have iter.len() < at(taken, iter.len());
            } else {
                step(); step(); step(); step(); step();
            }
        }
    }
    have loop(0).iter.len() == 0u64;
    have bytes.len() != 0u64 implies last == bytes.len() - 1u64 by {
        intro() {
            have loop(0).iter.count == bytes.len();
            close();
        }
    }
}

// A reference pattern binds the element's address, read by `*word`.
fn last_pair(words: &[u16]) -> u32 {
    views words[0..words.len()];
    ensures result <= 65535u32;
} by {
    step_until(loop(0).entry);
    loop {
        decreases iter.len();
        views words[0..words.len()];
        invariant iter.len() <= words.len();
        invariant iter.count == words.len() - iter.len();
        invariant iter.as_slice().as_ptr() == words.as_ptr() + iter.count;
        invariant iter.count != 0u64 implies index == iter.count - 1u64;
        invariant value <= 65535u32;
        maintain by {
            if 0u64 < iter.len() {
                mark taken;
                have to_integer(iter.count) < to_integer(words.len());
                have to_integer(iter.count) + 1 <= to_integer(words.len());
                have to_integer(iter.count) + 1 <= 18446744073709551615;
                apply(integer::uint64_add_to_integer(iter.count, 1u64));
                have to_integer(iter.count + 1u64) <= to_integer(words.len()) by {
                    rewrite(to_integer(iter.count + 1u64), to_integer(iter.count) + 1);
                    close();
                }
                have (words.as_ptr() + iter.count) + 1u64 == words.as_ptr() + (iter.count + 1u64);
                step_until(loop.back_edge);
                have iter.count == at(taken, iter.count) + 1u64;
                have iter.len() == at(taken, iter.len()) - 1u64;
                have iter.as_slice().as_ptr() == words.as_ptr() + iter.count;
                have index == iter.count - 1u64;
                have iter.len() < at(taken, iter.len());
            } else {
                step(); step(); step(); step(); step();
            }
        }
    }
}
