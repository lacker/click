verifying "span-probe.cpp";
std::span<std::byte> probe(std::span<int> span) {
    ensures std_span_data(result) == old(std_span_data(span) as (uint8 *));
    ensures std_span_size(result) == old(std_span_size(span)) * 4u64;
} by {
    step_until(call(0).entry);
    step();
    mark before_return;
    have std_span_data(call(0).parameter(__sp)) == old(std_span_data(span)) by { close(); }
    have std_span_size(call(0).parameter(__sp)) == old(std_span_size(span)) by { close(); }
    have std_span_size(call(0).result) == std_span_size(call(0).parameter(__sp)) * 4u64 by { close(); }
    have std_span_data(call(0).result) == old(std_span_data(span) as (uint8 *)) by { close(); }
    have separate(memory(at(call(0).exit, call(0).result)[0..8]), memory(at(before_return, span)[0])) by { close(); }
    have separate(memory(at(call(0).exit, call(0).result)[8..16]), memory(at(before_return, span)[0])) by { close(); }
    step_until(function.exit);
    have separate(region(1).footprint, memory(at(call(0).exit, call(0).result)[0..8])) by {
        normalize() using { separate(memory(at(call(0).exit, call(0).result)[0..8]), memory(at(before_return, span)[0])); };
    }
    have std_span_data(result) == std_span_data(call(0).result) by {
        preserve(memory(at(call(0).exit, call(0).result)[0..8]), region(1));
    }
    have std_span_size(call(0).parameter(__sp)) == old(std_span_size(span)) by { close(); }
    have std_span_size(call(0).result) == old(std_span_size(span)) * 4u64 by { close(); }
    have separate(region(1).footprint, memory(at(call(0).exit, call(0).result)[8..16])) by {
        normalize() using { separate(memory(at(call(0).exit, call(0).result)[8..16]), memory(at(before_return, span)[0])); };
    }
    have std_span_size(result) == std_span_size(call(0).result) by {
        preserve(memory(at(call(0).exit, call(0).result)[8..16]), region(1));
    }
    close();
}
