import click::integer;

theorem signed_offset_control(bytes: uint8[], prefix: int32, suffix: int32) {
    requires defined(prefix + suffix);
    ensures (bytes + prefix) + suffix == bytes + (prefix + suffix) by {
        normalize() using { defined(prefix + suffix); };
    }
}

theorem symbolic_unsigned_sum(bytes: uint8[], prefix: uint64, suffix: uint64, total: uint64) {
    requires to_integer(total) == to_integer(prefix) + to_integer(suffix);
    ensures (bytes + prefix) + suffix == bytes + total by {
        normalize() using {
            to_integer(total) == to_integer(prefix) + to_integer(suffix);
        };
    }
}
