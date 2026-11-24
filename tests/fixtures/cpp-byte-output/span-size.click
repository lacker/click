verifying "span-probe.cpp";

extern std::span<std::byte>::span(const std::span<std::byte>& source) {
    consumes uninitialized(this[0..1]);
    views std_span_data(source);
    views std_span_size(source);
    produces this[0..1];
    ensures std_span_data(this) == old(std_span_data(source));
    ensures std_span_size(this) == old(std_span_size(source));
}

uint64 length(std::span<std::byte> view) {
    requires std_span_size(view) == 4u64;
    ensures result == 4u64;
}

uint32 probe() {
    ensures result == 4u32;
} by {
    step_until(call(length, 0).entry);
    have std_span_size(dst) == 4u64 by { close(); }
    step() by { close(); }
}
