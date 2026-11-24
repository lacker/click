import click::separation;
verifying "span-probe.cpp";

void FixtureReader::read(std::span<std::byte> dst) {
    requires std_span_size(dst) == 4u64;
    requires 4u64 <= this->remaining;
    requires separate(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]));
    owns this->data;
    owns this->remaining;
    views this->data[0..4];
    consumes uninitialized(std_span_data(dst)[0..4]);
    produces std_span_data(dst)[0..4];
    ensures std_span_data(dst)[0] == old(this->data[0]);
    ensures std_span_data(dst)[1] == old(this->data[1]);
    ensures std_span_data(dst)[2] == old(this->data[2]);
    ensures std_span_data(dst)[3] == old(this->data[3]);
    ensures this->data == old(this->data) + 4;
    ensures this->remaining == old(this->remaining) - 4u64;
} by {
    have separate(memory(std_span_data(dst)[0..4]), memory(this->data)) by { close(); }
    have contains(memory(this->data[0..4]), memory(this->data[0..4])) by {
        apply(click::separation::contains_refl(memory(this->data[0..4])));
    }
    have contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[0])) by {
        apply(click::separation::contains_element(std_span_data(dst), 0, 4, 0));
    }
    have separate(memory(std_span_data(dst)[0]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]), memory(std_span_data(dst)[0]), memory(this->data[0..4])));
    }
    have contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[1])) by {
        apply(click::separation::contains_element(std_span_data(dst), 0, 4, 1));
    }
    have separate(memory(std_span_data(dst)[1]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]), memory(std_span_data(dst)[1]), memory(this->data[0..4])));
    }
    have contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[2])) by {
        apply(click::separation::contains_element(std_span_data(dst), 0, 4, 2));
    }
    have separate(memory(std_span_data(dst)[2]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]), memory(std_span_data(dst)[2]), memory(this->data[0..4])));
    }
    have contains(memory(std_span_data(dst)[0..4]), memory(std_span_data(dst)[3])) by {
        apply(click::separation::contains_element(std_span_data(dst), 0, 4, 3));
    }
    have separate(memory(std_span_data(dst)[3]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(std_span_data(dst)[0..4]), memory(this->data[0..4]), memory(std_span_data(dst)[3]), memory(this->data[0..4])));
    }
    step_until(call(0).entry);
    step();
    have call(0).result == old(std_span_data(dst)) + 0 by { close(); }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0..4])) by { close(); }
    step();
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->data)) by { close(); }
    have separate(region(2).footprint, memory(this->data)) by {
        normalize() using { separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->data)); };
    }
    have at(region(2).exit, this->data) == at(region(2).entry, this->data) by {
        preserve(memory(this->data), region(2));
    }
    have this->data == old(this->data) by { close(); }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->remaining)) by { close(); }
    have separate(region(2).footprint, memory(this->remaining)) by {
        normalize() using { separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->remaining)); };
    }
    have at(region(2).exit, this->remaining) == at(region(2).entry, this->remaining) by {
        preserve(memory(this->remaining), region(2));
    }
    have this->remaining == old(this->remaining) by { close(); }

    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0])) by { close(); }
    have separate(region(2).footprint, memory(old(this->data)[0])) by {
        normalize() using { separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0])); };
    }
    have at(region(2).exit, load<uint8>(old(this->data) + 0)) == at(region(2).entry, load<uint8>(old(this->data) + 0)) by {
        preserve(memory(old(this->data)[0]), region(2));
    }
    have load<uint8>(old(this->data) + 0) == old(this->data[0]) by { close(); }

    have load<uint8>(old(std_span_data(dst)) + 0) == old(this->data[0]) by { close(); }

    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[1])) by { close(); }
    have separate(region(2).footprint, memory(old(this->data)[1])) by {
        normalize() using { separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[1])); };
    }
    have at(region(2).exit, load<uint8>(old(this->data) + 1)) == at(region(2).entry, load<uint8>(old(this->data) + 1)) by {
        preserve(memory(old(this->data)[1]), region(2));
    }
    have load<uint8>(old(this->data) + 1) == old(this->data[1]) by { close(); }

    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[2])) by { close(); }
    have separate(region(2).footprint, memory(old(this->data)[2])) by {
        normalize() using { separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[2])); };
    }
    have at(region(2).exit, load<uint8>(old(this->data) + 2)) == at(region(2).entry, load<uint8>(old(this->data) + 2)) by {
        preserve(memory(old(this->data)[2]), region(2));
    }
    have load<uint8>(old(this->data) + 2) == old(this->data[2]) by { close(); }

    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[3])) by { close(); }
    have separate(region(2).footprint, memory(old(this->data)[3])) by {
        normalize() using { separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[3])); };
    }
    have at(region(2).exit, load<uint8>(old(this->data) + 3)) == at(region(2).entry, load<uint8>(old(this->data) + 3)) by {
        preserve(memory(old(this->data)[3]), region(2));
    }
    have load<uint8>(old(this->data) + 3) == old(this->data[3]) by { close(); }

    step_until(call(1).entry);
    step();
    have call(1).result == old(std_span_data(dst)) + 1 by { close(); }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0..4])) by { close(); }
    step();
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->data)) by { close(); }
    have separate(region(5).footprint, memory(this->data)) by {
        normalize() using { separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->data)); };
    }
    have at(region(5).exit, this->data) == at(region(5).entry, this->data) by {
        preserve(memory(this->data), region(5));
    }
    have this->data == old(this->data) by { close(); }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->remaining)) by { close(); }
    have separate(region(5).footprint, memory(this->remaining)) by {
        normalize() using { separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->remaining)); };
    }
    have at(region(5).exit, this->remaining) == at(region(5).entry, this->remaining) by {
        preserve(memory(this->remaining), region(5));
    }
    have this->remaining == old(this->remaining) by { close(); }

    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0])) by { close(); }
    have separate(region(5).footprint, memory(old(this->data)[0])) by {
        normalize() using { separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0])); };
    }
    have at(region(5).exit, load<uint8>(old(this->data) + 0)) == at(region(5).entry, load<uint8>(old(this->data) + 0)) by {
        preserve(memory(old(this->data)[0]), region(5));
    }
    have load<uint8>(old(this->data) + 0) == old(this->data[0]) by { close(); }

    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[1])) by { close(); }
    have separate(region(5).footprint, memory(old(this->data)[1])) by {
        normalize() using { separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[1])); };
    }
    have at(region(5).exit, load<uint8>(old(this->data) + 1)) == at(region(5).entry, load<uint8>(old(this->data) + 1)) by {
        preserve(memory(old(this->data)[1]), region(5));
    }
    have load<uint8>(old(this->data) + 1) == old(this->data[1]) by { close(); }

    have separate(memory(old(std_span_data(dst))[1]), memory(old(std_span_data(dst))[0])) by {
        apply(click::separation::separate_elements(old(std_span_data(dst)), 1, 0));
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(std_span_data(dst))[0])) by { close(); }
    have separate(region(5).footprint, memory(old(std_span_data(dst))[0])) by {
        normalize() using { separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(std_span_data(dst))[0])); };
    }
    have at(region(5).exit, load<uint8>(old(std_span_data(dst)) + 0)) == at(region(5).entry, load<uint8>(old(std_span_data(dst)) + 0)) by {
        preserve(memory(old(std_span_data(dst))[0]), region(5));
    }
    have load<uint8>(old(std_span_data(dst)) + 0) == old(this->data[0]) by { close(); }

    have load<uint8>(old(std_span_data(dst)) + 1) == old(this->data[1]) by { close(); }

    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[2])) by { close(); }
    have separate(region(5).footprint, memory(old(this->data)[2])) by {
        normalize() using { separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[2])); };
    }
    have at(region(5).exit, load<uint8>(old(this->data) + 2)) == at(region(5).entry, load<uint8>(old(this->data) + 2)) by {
        preserve(memory(old(this->data)[2]), region(5));
    }
    have load<uint8>(old(this->data) + 2) == old(this->data[2]) by { close(); }

    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[3])) by { close(); }
    have separate(region(5).footprint, memory(old(this->data)[3])) by {
        normalize() using { separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[3])); };
    }
    have at(region(5).exit, load<uint8>(old(this->data) + 3)) == at(region(5).entry, load<uint8>(old(this->data) + 3)) by {
        preserve(memory(old(this->data)[3]), region(5));
    }
    have load<uint8>(old(this->data) + 3) == old(this->data[3]) by { close(); }

    step_until(call(2).entry);
    step();
    have call(2).result == old(std_span_data(dst)) + 2 by { close(); }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0..4])) by { close(); }
    step();
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->data)) by { close(); }
    have separate(region(8).footprint, memory(this->data)) by {
        normalize() using { separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->data)); };
    }
    have at(region(8).exit, this->data) == at(region(8).entry, this->data) by {
        preserve(memory(this->data), region(8));
    }
    have this->data == old(this->data) by { close(); }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->remaining)) by { close(); }
    have separate(region(8).footprint, memory(this->remaining)) by {
        normalize() using { separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->remaining)); };
    }
    have at(region(8).exit, this->remaining) == at(region(8).entry, this->remaining) by {
        preserve(memory(this->remaining), region(8));
    }
    have this->remaining == old(this->remaining) by { close(); }

    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0])) by { close(); }
    have separate(region(8).footprint, memory(old(this->data)[0])) by {
        normalize() using { separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0])); };
    }
    have at(region(8).exit, load<uint8>(old(this->data) + 0)) == at(region(8).entry, load<uint8>(old(this->data) + 0)) by {
        preserve(memory(old(this->data)[0]), region(8));
    }
    have load<uint8>(old(this->data) + 0) == old(this->data[0]) by { close(); }

    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[1])) by { close(); }
    have separate(region(8).footprint, memory(old(this->data)[1])) by {
        normalize() using { separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[1])); };
    }
    have at(region(8).exit, load<uint8>(old(this->data) + 1)) == at(region(8).entry, load<uint8>(old(this->data) + 1)) by {
        preserve(memory(old(this->data)[1]), region(8));
    }
    have load<uint8>(old(this->data) + 1) == old(this->data[1]) by { close(); }

    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[2])) by { close(); }
    have separate(region(8).footprint, memory(old(this->data)[2])) by {
        normalize() using { separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[2])); };
    }
    have at(region(8).exit, load<uint8>(old(this->data) + 2)) == at(region(8).entry, load<uint8>(old(this->data) + 2)) by {
        preserve(memory(old(this->data)[2]), region(8));
    }
    have load<uint8>(old(this->data) + 2) == old(this->data[2]) by { close(); }

    have separate(memory(old(std_span_data(dst))[2]), memory(old(std_span_data(dst))[0])) by {
        apply(click::separation::separate_elements(old(std_span_data(dst)), 2, 0));
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(std_span_data(dst))[0])) by { close(); }
    have separate(region(8).footprint, memory(old(std_span_data(dst))[0])) by {
        normalize() using { separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(std_span_data(dst))[0])); };
    }
    have at(region(8).exit, load<uint8>(old(std_span_data(dst)) + 0)) == at(region(8).entry, load<uint8>(old(std_span_data(dst)) + 0)) by {
        preserve(memory(old(std_span_data(dst))[0]), region(8));
    }
    have load<uint8>(old(std_span_data(dst)) + 0) == old(this->data[0]) by { close(); }

    have separate(memory(old(std_span_data(dst))[2]), memory(old(std_span_data(dst))[1])) by {
        apply(click::separation::separate_elements(old(std_span_data(dst)), 2, 1));
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(std_span_data(dst))[1])) by { close(); }
    have separate(region(8).footprint, memory(old(std_span_data(dst))[1])) by {
        normalize() using { separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(std_span_data(dst))[1])); };
    }
    have at(region(8).exit, load<uint8>(old(std_span_data(dst)) + 1)) == at(region(8).entry, load<uint8>(old(std_span_data(dst)) + 1)) by {
        preserve(memory(old(std_span_data(dst))[1]), region(8));
    }
    have load<uint8>(old(std_span_data(dst)) + 1) == old(this->data[1]) by { close(); }

    have load<uint8>(old(std_span_data(dst)) + 2) == old(this->data[2]) by { close(); }

    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[3])) by { close(); }
    have separate(region(8).footprint, memory(old(this->data)[3])) by {
        normalize() using { separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[3])); };
    }
    have at(region(8).exit, load<uint8>(old(this->data) + 3)) == at(region(8).entry, load<uint8>(old(this->data) + 3)) by {
        preserve(memory(old(this->data)[3]), region(8));
    }
    have load<uint8>(old(this->data) + 3) == old(this->data[3]) by { close(); }

    step_until(call(3).entry);
    step();
    have call(3).result == old(std_span_data(dst)) + 3 by { close(); }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0..4])) by { close(); }
    step();
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->data)) by { close(); }
    have separate(region(11).footprint, memory(this->data)) by {
        normalize() using { separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->data)); };
    }
    have at(region(11).exit, this->data) == at(region(11).entry, this->data) by {
        preserve(memory(this->data), region(11));
    }
    have this->data == old(this->data) by { close(); }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->remaining)) by { close(); }
    have separate(region(11).footprint, memory(this->remaining)) by {
        normalize() using { separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->remaining)); };
    }
    have at(region(11).exit, this->remaining) == at(region(11).entry, this->remaining) by {
        preserve(memory(this->remaining), region(11));
    }
    have this->remaining == old(this->remaining) by { close(); }

    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0])) by { close(); }
    have separate(region(11).footprint, memory(old(this->data)[0])) by {
        normalize() using { separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0])); };
    }
    have at(region(11).exit, load<uint8>(old(this->data) + 0)) == at(region(11).entry, load<uint8>(old(this->data) + 0)) by {
        preserve(memory(old(this->data)[0]), region(11));
    }
    have load<uint8>(old(this->data) + 0) == old(this->data[0]) by { close(); }

    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[1])) by { close(); }
    have separate(region(11).footprint, memory(old(this->data)[1])) by {
        normalize() using { separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[1])); };
    }
    have at(region(11).exit, load<uint8>(old(this->data) + 1)) == at(region(11).entry, load<uint8>(old(this->data) + 1)) by {
        preserve(memory(old(this->data)[1]), region(11));
    }
    have load<uint8>(old(this->data) + 1) == old(this->data[1]) by { close(); }

    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[2])) by { close(); }
    have separate(region(11).footprint, memory(old(this->data)[2])) by {
        normalize() using { separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[2])); };
    }
    have at(region(11).exit, load<uint8>(old(this->data) + 2)) == at(region(11).entry, load<uint8>(old(this->data) + 2)) by {
        preserve(memory(old(this->data)[2]), region(11));
    }
    have load<uint8>(old(this->data) + 2) == old(this->data[2]) by { close(); }

    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[3])) by { close(); }
    have separate(region(11).footprint, memory(old(this->data)[3])) by {
        normalize() using { separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[3])); };
    }
    have at(region(11).exit, load<uint8>(old(this->data) + 3)) == at(region(11).entry, load<uint8>(old(this->data) + 3)) by {
        preserve(memory(old(this->data)[3]), region(11));
    }
    have load<uint8>(old(this->data) + 3) == old(this->data[3]) by { close(); }

    have separate(memory(old(std_span_data(dst))[3]), memory(old(std_span_data(dst))[0])) by {
        apply(click::separation::separate_elements(old(std_span_data(dst)), 3, 0));
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(std_span_data(dst))[0])) by { close(); }
    have separate(region(11).footprint, memory(old(std_span_data(dst))[0])) by {
        normalize() using { separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(std_span_data(dst))[0])); };
    }
    have at(region(11).exit, load<uint8>(old(std_span_data(dst)) + 0)) == at(region(11).entry, load<uint8>(old(std_span_data(dst)) + 0)) by {
        preserve(memory(old(std_span_data(dst))[0]), region(11));
    }
    have load<uint8>(old(std_span_data(dst)) + 0) == old(this->data[0]) by { close(); }

    have separate(memory(old(std_span_data(dst))[3]), memory(old(std_span_data(dst))[1])) by {
        apply(click::separation::separate_elements(old(std_span_data(dst)), 3, 1));
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(std_span_data(dst))[1])) by { close(); }
    have separate(region(11).footprint, memory(old(std_span_data(dst))[1])) by {
        normalize() using { separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(std_span_data(dst))[1])); };
    }
    have at(region(11).exit, load<uint8>(old(std_span_data(dst)) + 1)) == at(region(11).entry, load<uint8>(old(std_span_data(dst)) + 1)) by {
        preserve(memory(old(std_span_data(dst))[1]), region(11));
    }
    have load<uint8>(old(std_span_data(dst)) + 1) == old(this->data[1]) by { close(); }

    have separate(memory(old(std_span_data(dst))[3]), memory(old(std_span_data(dst))[2])) by {
        apply(click::separation::separate_elements(old(std_span_data(dst)), 3, 2));
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(std_span_data(dst))[2])) by { close(); }
    have separate(region(11).footprint, memory(old(std_span_data(dst))[2])) by {
        normalize() using { separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(std_span_data(dst))[2])); };
    }
    have at(region(11).exit, load<uint8>(old(std_span_data(dst)) + 2)) == at(region(11).entry, load<uint8>(old(std_span_data(dst)) + 2)) by {
        preserve(memory(old(std_span_data(dst))[2]), region(11));
    }
    have load<uint8>(old(std_span_data(dst)) + 2) == old(this->data[2]) by { close(); }

    have load<uint8>(old(std_span_data(dst)) + 3) == old(this->data[3]) by { close(); }

    have separate(memory((this as (uint64 *))[0..1]), memory(old(this->data)[0..4])) by { close(); }
    step();
    have separate(memory((&this->remaining)[0..1]), memory(old(this->data)[0..4])) by { close(); }
    step();
    step_until(function.exit);

    have separate(memory(this->data), memory(old(std_span_data(dst))[0])) by { close(); }
    have separate(region(12).footprint, memory(old(std_span_data(dst))[0])) by {
        normalize() using { separate(memory(this->data), memory(old(std_span_data(dst))[0])); };
    }
    have at(region(12).exit, load<uint8>(old(std_span_data(dst)) + 0)) == at(region(12).entry, load<uint8>(old(std_span_data(dst)) + 0)) by {
        preserve(memory(old(std_span_data(dst))[0]), region(12));
    }
    have at(region(12).exit, load<uint8>(old(std_span_data(dst)) + 0)) == old(this->data[0]) by { close(); }

    have separate(memory(this->data), memory(old(std_span_data(dst))[1])) by { close(); }
    have separate(region(12).footprint, memory(old(std_span_data(dst))[1])) by {
        normalize() using { separate(memory(this->data), memory(old(std_span_data(dst))[1])); };
    }
    have at(region(12).exit, load<uint8>(old(std_span_data(dst)) + 1)) == at(region(12).entry, load<uint8>(old(std_span_data(dst)) + 1)) by {
        preserve(memory(old(std_span_data(dst))[1]), region(12));
    }
    have at(region(12).exit, load<uint8>(old(std_span_data(dst)) + 1)) == old(this->data[1]) by { close(); }

    have separate(memory(this->data), memory(old(std_span_data(dst))[2])) by { close(); }
    have separate(region(12).footprint, memory(old(std_span_data(dst))[2])) by {
        normalize() using { separate(memory(this->data), memory(old(std_span_data(dst))[2])); };
    }
    have at(region(12).exit, load<uint8>(old(std_span_data(dst)) + 2)) == at(region(12).entry, load<uint8>(old(std_span_data(dst)) + 2)) by {
        preserve(memory(old(std_span_data(dst))[2]), region(12));
    }
    have at(region(12).exit, load<uint8>(old(std_span_data(dst)) + 2)) == old(this->data[2]) by { close(); }

    have separate(memory(this->data), memory(old(std_span_data(dst))[3])) by { close(); }
    have separate(region(12).footprint, memory(old(std_span_data(dst))[3])) by {
        normalize() using { separate(memory(this->data), memory(old(std_span_data(dst))[3])); };
    }
    have at(region(12).exit, load<uint8>(old(std_span_data(dst)) + 3)) == at(region(12).entry, load<uint8>(old(std_span_data(dst)) + 3)) by {
        preserve(memory(old(std_span_data(dst))[3]), region(12));
    }
    have at(region(12).exit, load<uint8>(old(std_span_data(dst)) + 3)) == old(this->data[3]) by { close(); }

    have separate(memory(this->remaining), memory(old(std_span_data(dst))[0])) by { close(); }
    have separate(region(13).footprint, memory(old(std_span_data(dst))[0])) by {
        normalize() using { separate(memory(this->remaining), memory(old(std_span_data(dst))[0])); };
    }
    have at(region(13).exit, load<uint8>(old(std_span_data(dst)) + 0)) == at(region(13).entry, load<uint8>(old(std_span_data(dst)) + 0)) by {
        preserve(memory(old(std_span_data(dst))[0]), region(13));
    }
    have at(region(13).exit, load<uint8>(old(std_span_data(dst)) + 0)) == old(this->data[0]) by { close(); }

    have separate(memory(this->remaining), memory(old(std_span_data(dst))[1])) by { close(); }
    have separate(region(13).footprint, memory(old(std_span_data(dst))[1])) by {
        normalize() using { separate(memory(this->remaining), memory(old(std_span_data(dst))[1])); };
    }
    have at(region(13).exit, load<uint8>(old(std_span_data(dst)) + 1)) == at(region(13).entry, load<uint8>(old(std_span_data(dst)) + 1)) by {
        preserve(memory(old(std_span_data(dst))[1]), region(13));
    }
    have at(region(13).exit, load<uint8>(old(std_span_data(dst)) + 1)) == old(this->data[1]) by { close(); }

    have separate(memory(this->remaining), memory(old(std_span_data(dst))[2])) by { close(); }
    have separate(region(13).footprint, memory(old(std_span_data(dst))[2])) by {
        normalize() using { separate(memory(this->remaining), memory(old(std_span_data(dst))[2])); };
    }
    have at(region(13).exit, load<uint8>(old(std_span_data(dst)) + 2)) == at(region(13).entry, load<uint8>(old(std_span_data(dst)) + 2)) by {
        preserve(memory(old(std_span_data(dst))[2]), region(13));
    }
    have at(region(13).exit, load<uint8>(old(std_span_data(dst)) + 2)) == old(this->data[2]) by { close(); }

    have separate(memory(this->remaining), memory(old(std_span_data(dst))[3])) by { close(); }
    have separate(region(13).footprint, memory(old(std_span_data(dst))[3])) by {
        normalize() using { separate(memory(this->remaining), memory(old(std_span_data(dst))[3])); };
    }
    have at(region(13).exit, load<uint8>(old(std_span_data(dst)) + 3)) == at(region(13).entry, load<uint8>(old(std_span_data(dst)) + 3)) by {
        preserve(memory(old(std_span_data(dst))[3]), region(13));
    }
    have at(region(13).exit, load<uint8>(old(std_span_data(dst)) + 3)) == old(this->data[3]) by { close(); }

    have separate(memory(this->data), memory(old(this->data)[0])) by { close(); }
    have separate(region(12).footprint, memory(old(this->data)[0])) by {
        normalize() using { separate(memory(this->data), memory(old(this->data)[0])); };
    }
    have at(region(12).exit, load<uint8>(old(this->data) + 0)) == at(region(12).entry, load<uint8>(old(this->data) + 0)) by {
        preserve(memory(old(this->data)[0]), region(12));
    }
    have at(region(12).exit, load<uint8>(old(this->data) + 0)) == old(this->data[0]) by { close(); }

    have separate(memory(this->data), memory(old(this->data)[1])) by { close(); }
    have separate(region(12).footprint, memory(old(this->data)[1])) by {
        normalize() using { separate(memory(this->data), memory(old(this->data)[1])); };
    }
    have at(region(12).exit, load<uint8>(old(this->data) + 1)) == at(region(12).entry, load<uint8>(old(this->data) + 1)) by {
        preserve(memory(old(this->data)[1]), region(12));
    }
    have at(region(12).exit, load<uint8>(old(this->data) + 1)) == old(this->data[1]) by { close(); }

    have separate(memory(this->data), memory(old(this->data)[2])) by { close(); }
    have separate(region(12).footprint, memory(old(this->data)[2])) by {
        normalize() using { separate(memory(this->data), memory(old(this->data)[2])); };
    }
    have at(region(12).exit, load<uint8>(old(this->data) + 2)) == at(region(12).entry, load<uint8>(old(this->data) + 2)) by {
        preserve(memory(old(this->data)[2]), region(12));
    }
    have at(region(12).exit, load<uint8>(old(this->data) + 2)) == old(this->data[2]) by { close(); }

    have separate(memory(this->data), memory(old(this->data)[3])) by { close(); }
    have separate(region(12).footprint, memory(old(this->data)[3])) by {
        normalize() using { separate(memory(this->data), memory(old(this->data)[3])); };
    }
    have at(region(12).exit, load<uint8>(old(this->data) + 3)) == at(region(12).entry, load<uint8>(old(this->data) + 3)) by {
        preserve(memory(old(this->data)[3]), region(12));
    }
    have at(region(12).exit, load<uint8>(old(this->data) + 3)) == old(this->data[3]) by { close(); }

    have separate(memory(this->remaining), memory(old(this->data)[0])) by { close(); }
    have separate(region(13).footprint, memory(old(this->data)[0])) by {
        normalize() using { separate(memory(this->remaining), memory(old(this->data)[0])); };
    }
    have at(region(13).exit, load<uint8>(old(this->data) + 0)) == at(region(13).entry, load<uint8>(old(this->data) + 0)) by {
        preserve(memory(old(this->data)[0]), region(13));
    }
    have at(region(13).exit, load<uint8>(old(this->data) + 0)) == old(this->data[0]) by { close(); }

    have separate(memory(this->remaining), memory(old(this->data)[1])) by { close(); }
    have separate(region(13).footprint, memory(old(this->data)[1])) by {
        normalize() using { separate(memory(this->remaining), memory(old(this->data)[1])); };
    }
    have at(region(13).exit, load<uint8>(old(this->data) + 1)) == at(region(13).entry, load<uint8>(old(this->data) + 1)) by {
        preserve(memory(old(this->data)[1]), region(13));
    }
    have at(region(13).exit, load<uint8>(old(this->data) + 1)) == old(this->data[1]) by { close(); }

    have separate(memory(this->remaining), memory(old(this->data)[2])) by { close(); }
    have separate(region(13).footprint, memory(old(this->data)[2])) by {
        normalize() using { separate(memory(this->remaining), memory(old(this->data)[2])); };
    }
    have at(region(13).exit, load<uint8>(old(this->data) + 2)) == at(region(13).entry, load<uint8>(old(this->data) + 2)) by {
        preserve(memory(old(this->data)[2]), region(13));
    }
    have at(region(13).exit, load<uint8>(old(this->data) + 2)) == old(this->data[2]) by { close(); }

    have separate(memory(this->remaining), memory(old(this->data)[3])) by { close(); }
    have separate(region(13).footprint, memory(old(this->data)[3])) by {
        normalize() using { separate(memory(this->remaining), memory(old(this->data)[3])); };
    }
    have at(region(13).exit, load<uint8>(old(this->data) + 3)) == at(region(13).entry, load<uint8>(old(this->data) + 3)) by {
        preserve(memory(old(this->data)[3]), region(13));
    }
    have at(region(13).exit, load<uint8>(old(this->data) + 3)) == old(this->data[3]) by { close(); }

    have separate(memory(this->data), memory(this->remaining)) by { close(); }
    have separate(region(12).footprint, memory(this->remaining)) by {
        normalize() using { separate(memory(this->data), memory(this->remaining)); };
    }
    have at(region(12).exit, this->remaining) == at(region(12).entry, this->remaining) by {
        preserve(memory(this->remaining), region(12));
    }
    have at(region(12).exit, this->remaining) == old(this->remaining) by { close(); }
    have this->remaining == old(this->remaining) - 4u64 by { close(); }
    close();
}

uint32 le32toh_internal(uint32 little_endian_32bits) {
    ensures result == little_endian_32bits;
}

uint32 ser_readdata32<FixtureReader>(struct FixtureReader& s) {
    requires 4u64 <= s.remaining;
    requires s.data[0] == 120u8;
    requires s.data[1] == 86u8;
    requires s.data[2] == 52u8;
    requires s.data[3] == 18u8;
    owns s.data;
    owns s.remaining;
    views s.data[0..4];
    ensures result == 305419896u32;
    ensures s.data == old(s.data) + 4;
    ensures s.remaining == old(s.remaining) - 4u64;
} by {
    step_until(call(1).entry);
    step();
    have std_span_size(call(1).parameter(__sp)) == 1u64 by { close(); }
    have std_span_data(call(1).parameter(__sp)) == &obj by { close(); }
    have std_span_size(call(1).result) == std_span_size(call(1).parameter(__sp)) * 4u64 by { close(); }
    have std_span_size(call(1).result) == 4u64 by { close(); }
    have std_span_data(call(1).result) == ((&obj) as (uint8 *)) by { close(); }
    step_until(call(2).entry);
    step() {
        requires std_span_size(call(2).parameter(dst)) == 4u64 by { close(); }
        requires 4u64 <= s.remaining by { close(); }
        requires separate(memory(at(call(2).entry, std_span_data(call(2).parameter(dst)))[0..4]), memory(s.data[0..4])) by { close(); }
        requires separate(memory(at(call(2).entry, load<uint8*>(region(4).result))[0..4]), memory(s.data[0..4])) by { close(); }
    }
    have std_span_data(call(2).parameter(dst)) == ((&obj) as (uint8 *)) by { close(); }
    have ((&obj) as (uint8 *))[0] == 120u8 by { close(); }
    have ((&obj) as (uint8 *))[1] == 86u8 by { close(); }
    have ((&obj) as (uint8 *))[2] == 52u8 by { close(); }
    have ((&obj) as (uint8 *))[3] == 18u8 by { close(); }
    have obj == 305419896u32 by { close(); }
    step_until(function.exit);
    close();
}

uint32 probe(struct FixtureReader& stream) {
    requires 4u64 <= stream.remaining;
    requires stream.data[0] == 120u8;
    requires stream.data[1] == 86u8;
    requires stream.data[2] == 52u8;
    requires stream.data[3] == 18u8;
    owns stream.data;
    owns stream.remaining;
    views stream.data[0..4];
    ensures result == 305419896u32;
    ensures stream.data == old(stream.data) + 4;
    ensures stream.remaining == old(stream.remaining) - 4u64;
}
