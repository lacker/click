verifying "span-probe.cpp";

extern std::span<std::byte>::span(const std::span<std::byte>& source) {
    consumes uninitialized(this[0..1]);
    views std_span_data(source);
    views std_span_size(source);
    produces this[0..1];
    ensures std_span_data(this) == old(std_span_data(source));
    ensures std_span_size(this) == old(std_span_size(source));
}

void fill(std::span<std::byte> dst) {
    requires std_span_size(dst) == 4u64;
    consumes uninitialized(std_span_data(dst)[0..4]);
    produces std_span_data(dst)[0..4];
    ensures std_span_data(dst)[0] == 120u8;
    ensures std_span_data(dst)[1] == 86u8;
    ensures std_span_data(dst)[2] == 52u8;
    ensures std_span_data(dst)[3] == 18u8;
}

uint32 probe() {
    ensures result == 305419896u32;
} by {
    step_until(call(fill, 0).entry);
    have std_span_size(dst) == 4u64 by { close(); }
    step();
    have std_span_data(dst) == ((&obj) as (uint8*)) by { close(); }
    have ((&obj) as (uint8*))[0] == 120u8 by { close(); }
    have ((&obj) as (uint8*))[1] == 86u8 by { close(); }
    have ((&obj) as (uint8*))[2] == 52u8 by { close(); }
    have ((&obj) as (uint8*))[3] == 18u8 by { close(); }
    step_until(function.exit);
    close();
}
