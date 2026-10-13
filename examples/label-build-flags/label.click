verifying "label_fit.c";
verifying "label_copy.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
} by {
    execute();
    have result <= length by auto;
    simp();
}

theorem label_source_prefix_viewable(bytes: uint8[], length: uint64, taken: uint64) {
    requires length < 18446744073709551615u64;
    requires length + 1u64 <= 9223372036854775807u64;
    requires viewable(bytes[0u64..length + 1u64]);
    requires taken <= length;
    ensures viewable(bytes[0u64..taken]) by {
        apply(uint64_less_than_to_integer(length, 18446744073709551615u64));
        apply(uint64_less_equal_to_integer(taken, length));
        have to_integer(length) + 1 <= 18446744073709551615 by { auto; }
        apply(uint64_add_to_integer(length, 1u64));
        have to_integer(taken) <= to_integer(length + 1u64) by { auto; }
        apply(uint64_to_integer_less_equal_implies_less_equal(taken, length + 1u64));
        apply(uint64_less_equal_transitive(taken, length + 1u64, 9223372036854775807u64));
        simp() using {
            taken <= length + 1u64;
            taken <= 9223372036854775807u64;
            viewable(bytes[0u64..length + 1u64]);
        };
    }
}

uint64 label_measure(const char* src) {
    requires cstr_readable(src);
    ensures result < 32;
} by {
    execute();
    simp();
}

uint64 label_copy(char* dst, const char* src) {
    requires cstr_readable(src);
    owns dst[0u64..32u64];
    requires separate(memory(dst[0u64..32u64]), memory(src[0u64..32u64]));
    ensures result < 32;
    ensures dst[result] == '\0';
} by {
    step();
    unfold(cstr_readable);
    have exists (len: uint64) {
        len < 18446744073709551615u64 and
        viewable(((uint8*)src)[0..len + 1u64]) and
        forall (k: uint64) { k < len implies ((uint8*)src)[k] != 0u8 } and
        ((uint8*)src)[len] == 0u8 and
        forall (k: uint64) { k < len + 1u64 implies defined(((uint8*)src)[k]) }
    } by {
        obtain (len: uint64) { at(function.entry,
            len < 18446744073709551615u64 and
            viewable(((uint8*)src)[0..len + 1u64]) and
            forall (k: uint64) { k < len implies ((uint8*)src)[k] != 0u8 } and
            ((uint8*)src)[len] == 0u8 and
            forall (k: uint64) { k < len + 1u64 implies defined(((uint8*)src)[k]) }
        ) }
        witness { len: len };
        extract(at(function.entry, len) < at(function.entry, 18446744073709551615u64));
        transport(at(function.entry, viewable(((uint8*)src)[0..len + 1u64])),
                  viewable(((uint8*)src)[0..len + 1u64])) using {
            at(function.entry, viewable(((uint8*)src)[0..len + 1u64]));
        }
        have forall (k: uint64) { k < len + 1u64 implies defined(((uint8*)src)[k]) } by {
            extract(at(function.entry, forall (k: uint64) {
                k < len + 1u64 implies defined(((uint8*)src)[k])
            }));
            intro();
            intro();
            instantiate(at(function.entry, forall (k: uint64) {
                k < len + 1u64 implies defined(((uint8*)src)[k])
            }), k) using { k < len + 1u64; }
            transport(at(function.entry, defined(((uint8*)src)[k])),
                      defined(((uint8*)src)[k])) using {
                at(function.entry, defined(((uint8*)src)[k]));
            }
        }
        extract(at(function.entry, forall (k: uint64) { k < len implies ((uint8*)src)[k] != 0u8 }));
        extract(at(function.entry, ((uint8*)src)[len] == 0u8));
        simp();
    }
    let length = step(strlen(src), {});
    let taken = step(label_fit(length), {});
    have viewable(((uint8*)src)[0u64..length + 1u64]) by {
        transport(at(statement(2).entry, viewable(((uint8*)src)[0u64..length + 1u64])),
                  viewable(((uint8*)src)[0u64..length + 1u64])) using {
            at(statement(2).entry, viewable(((uint8*)src)[0u64..length + 1u64]));
        }
    }
    apply(label_source_prefix_viewable(((uint8*)src), length, taken));
    execute();
    simp();
}
