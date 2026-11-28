import click::integer;
import click::rust::slice;

verifying "sum.rs";
function prefix(bytes: &[u8], end: usize) -> Integer {
    (0..end).fold(0, |acc, k| {
        acc + to_integer(bytes[k] as i32)
    })
}
theorem pointer_association(base: const uint8*, p: uint64, q: uint64) {
    requires to_integer(p) + to_integer(q) <= 18446744073709551615;
    ensures (base + p) + q == base + (p + q) by {
        apply(integer::uint64_add_to_integer(p, q));
        close() using { to_integer(p + q) == to_integer(p) + to_integer(q); };
    }
}
theorem read_same_byte(base: const uint8*, alias: const uint8*) {
    requires base == alias;
    requires viewable(memory(*base));
    ensures *alias == *base by {
        rewrite(alias, base);
        close();
    }
}
fn sum(bytes: &[u8]) -> i32 {
    requires bytes.len() <= 1000u64;
    views bytes[0..bytes.len()];
    ensures result == old(prefix(bytes, bytes.len()));
} by {
    step_until(loop(0).entry);
    have loop(0).iter.len() == bytes.len();
    have loop(0).iter.as_slice().as_ptr() == bytes.as_ptr();
    have bytes.len() - loop(0).iter.len() == 0u64;
    have prefix(bytes, bytes.len() - loop(0).iter.len()) == 0 by {
        rewrite(bytes.len() - loop(0).iter.len(), 0u64);
        have 0u64 <= 0u64;
        unfold(prefix(bytes, 0u64));
        close();
    }
    have 0 <= total and to_integer(total) <= 255 * (to_integer(bytes.len()) - to_integer(loop(0).iter.len()));
    have total == prefix(bytes, bytes.len() - loop(0).iter.len());
    loop {
        decreases iter.len();
        views bytes[0..bytes.len()];
        invariant bytes.len() <= 1000u64;
        invariant iter.len() <= bytes.len();
        invariant iter.as_slice().as_ptr() == bytes.as_ptr() + (bytes.len() - iter.len());
        invariant 0 <= total and to_integer(total) <= 255 * (to_integer(bytes.len()) - to_integer(iter.len()));
        invariant total == prefix(bytes, bytes.len() - iter.len());
        maintain by {
            if 0u64 < iter.len() {
                mark iteration;
                have to_integer(total) <= 255000 by {
                    close() using {
                        to_integer(total) <= 255 * (to_integer(bytes.len()) - to_integer(iter.len()));
                        iter.len() <= bytes.len();
                        bytes.len() <= 1000u64;
                    };
                }
                have 0 <= to_integer(bytes.len() - iter.len());
                have to_integer(bytes.len() - iter.len()) < 18446744073709551615;
                have prefix(bytes, (bytes.len() - iter.len()) + 1u64) == prefix(bytes, (bytes.len() - iter.len())) + to_integer(bytes[(bytes.len() - iter.len())] as i32) by {
                    unfold(prefix(bytes, (bytes.len() - iter.len()) + 1u64));
                    close();
                }
                have to_integer(bytes.len() - iter.len()) + 1 <= 18446744073709551615;
                have viewable(bytes[0u64..bytes.len()]) by {
                    observe(bytes[0u64..bytes.len()]);
                }
                have bytes.len() - iter.len() < bytes.len();
                have contains(memory(bytes[0u64..bytes.len()]), memory(bytes[(bytes.len() - iter.len())])) by {
                    apply(click::separation::contains_element(bytes.as_ptr(), 0u64, bytes.len(), bytes.len() - iter.len()));
                }
                have viewable(memory(bytes[(bytes.len() - iter.len())])) by {
                    apply(click::separation::viewable_restrict(memory(bytes[0u64..bytes.len()]), memory(bytes[(bytes.len() - iter.len())])));
                }
                have *iter.as_slice().as_ptr() == bytes[(bytes.len() - iter.len())] by {
                    apply(read_same_byte(bytes.as_ptr() + (bytes.len() - iter.len()), iter.as_slice().as_ptr()));
                    close();
                }
                step_until(loop(0).statement(0).entry);
                have iter.len() == at(iteration, iter.len()) - 1u64;
                have iter.as_slice().as_ptr() == (bytes.as_ptr() + (bytes.len() - at(iteration, iter.len()))) + 1u64;
                apply(pointer_association(bytes.as_ptr(), bytes.len() - at(iteration, iter.len()), 1u64));
                have at(iteration, *iter.as_slice().as_ptr()) == byte;
                have at(iteration, bytes[(bytes.len() - iter.len())]) == byte;
                have defined(total + byte as i32) by {
                    close() using { 0 <= total; to_integer(total) <= 255000; };
                }
                mark before_total_write;
                have to_integer(total + byte as i32) == to_integer(total) + to_integer(byte as i32);
                have 0 <= to_integer(at(before_total_write, total)) + to_integer(byte as i32) by {
                    close() using { 0 <= total; };
                }
                step_until(assignment(total, 1).entry); step();
                step_until(loop.back_edge);
                have to_integer(iter.len()) == to_integer(at(iteration, iter.len())) - 1;
                have to_integer(iter.len()) <= to_integer(bytes.len());
                apply(integer::uint64_subtract_to_integer(bytes.len(), iter.len()));
                have to_integer(at(iteration, iter.len())) <= to_integer(bytes.len());
                apply(integer::uint64_subtract_to_integer(bytes.len(), at(iteration, iter.len())));
                apply(integer::uint64_add_to_integer(bytes.len() - at(iteration, iter.len()), 1u64));
                have to_integer(bytes.len() - iter.len()) == to_integer((bytes.len() - at(iteration, iter.len())) + 1u64);
                have iter.len() <= bytes.len();
                have iter.as_slice().as_ptr() == bytes.as_ptr() + (bytes.len() - iter.len()) by {
                    rewrite((bytes.len() - iter.len()), (bytes.len() - at(iteration, iter.len())) + 1u64);
                    close();
                }
                have iter.len() < at(iteration, iter.len());
                have to_integer(total) == to_integer(at(before_total_write, total)) + to_integer(byte as i32) by { close(); }
                have 0 <= total by {
                    close() using {
                        0 <= to_integer(at(before_total_write, total)) + to_integer(byte as i32);
                        to_integer(total) == to_integer(at(before_total_write, total)) + to_integer(byte as i32);
                    };
                }
                have to_integer(total) <= 255 * (to_integer(bytes.len()) - to_integer(iter.len()));
            } else {
                have iter.len() == 0u64;
                step(); step(); step(); step(); step();
            }
        }
    }
    have loop(0).iter.len() == 0u64;
    have prefix(bytes, bytes.len() - loop(0).iter.len()) == prefix(bytes, bytes.len()) by {
        rewrite(loop(0).iter.len(), 0u64);
        close();
    }
}
