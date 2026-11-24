verifying "span-probe.cpp";

std::span<std::byte> probe(const std::span<int>& span) {
    views std_span_data(span);
    views std_span_size(span);
    ensures std_span_data(result) == std_span_data(span) as (uint8 *);
    ensures std_span_size(result) == std_span_size(span) * 4u64;
    ensures std_span_data(span) == old(std_span_data(span));
    ensures std_span_size(span) == old(std_span_size(span));
} by {
    have separate(memory(((&result) as (uint8 *))[0..16]), memory(std_span_data(span))) by { close(); }
    have separate(memory(((&result) as (uint8 *))[0..16]), memory(std_span_size(span))) by { close(); }
    step() {
        requires separate(
            memory(((&result) as (uint8 *))[0..16]),
            memory(std_span_data(span)) * memory(std_span_size(span))
        ) by { close(); }
    }
    step_until(function.exit);
    close();
}
