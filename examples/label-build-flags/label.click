import click::bytes;
import click::c::string::{cstr_at};
import click::separation;

verifying "label_fit.c";
verifying "label_copy.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
    ensures length < 32u64 implies result == length;
    ensures 32u64 <= length implies result == 31u64;
}

uint64 label_measure(const char* src) {
    let n: uint64;
    views cstr_at(src, n);
    ensures n < 32u64 implies result == n;
    ensures 32u64 <= n implies result == 31u64;
}

uint64 label_copy(char* dst, const char* src) {
    let len: uint64;
    views cstr_at(src, len);
    owns dst[0u64..32u64];
    requires separate(memory(dst[0u64..32u64]), memory(src[0u64..len + 1u64]));
    ensures len < 32u64 implies result == len;
    ensures 32u64 <= len implies result == 31u64;
    ensures dst[result] == '\0';
    ensures bytes::equal(dst, 0u64, src, 0u64, result);
} by {
    step();
    step();
    step();
    step();
    have 0u64 <= n by { normalize(); }
    have n < 32u64 by { solve(); }
    have contains(memory(dst[0u64..32u64]), memory(dst[n])) by {
        apply(separation::contains_element(dst, 0u64, 32u64, n)) using { 0u64 <= n; n < 32u64; };
    }
    have separate(memory(dst[n]), memory(src[0u64..len + 1u64])) by { solve(); }
    open(cstr_at(src, len)) {
        step();
        mark copied;
        unfold(at(copied, bytes::equal(dst, 0u64, old(src), 0u64, n)));
        step();
        have bytes::equal(dst, 0u64, src, 0u64, n) by {
            unfold(bytes::equal(dst, 0u64, src, 0u64, n));
            transport(
                at(copied, (0u64..n).all(|k| {
                    (dst as (uint8 *))[0u64 + k] == old((src as (uint8 *))[0u64 + k])
                })),
                (0u64..n).all(|k| { (dst as (uint8 *))[0u64 + k] == (src as (uint8 *))[0u64 + k] })
            );
        }
        step_until(function.exit);
    }
}
