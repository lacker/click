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
    have separate(memory(dst->_M_ptr[0..4]), memory(this->data)) by {
        close();
    }
    have contains(memory(this->data[0..4]), memory(this->data[0..4])) by {
        apply(click::separation::contains_refl(memory(this->data[0..4])));
    }
    have contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[0])) by {
        apply(click::separation::contains_element(dst->_M_ptr, 0, 4, 0));
    }
    have separate(memory(dst->_M_ptr[0]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]), memory(dst->_M_ptr[0]), memory(this->data[0..4])));
    }
    have contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[1])) by {
        apply(click::separation::contains_element(dst->_M_ptr, 0, 4, 1));
    }
    have separate(memory(dst->_M_ptr[1]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]), memory(dst->_M_ptr[1]), memory(this->data[0..4])));
    }
    have contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[2])) by {
        apply(click::separation::contains_element(dst->_M_ptr, 0, 4, 2));
    }
    have separate(memory(dst->_M_ptr[2]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]), memory(dst->_M_ptr[2]), memory(this->data[0..4])));
    }
    have contains(memory(dst->_M_ptr[0..4]), memory(dst->_M_ptr[3])) by {
        apply(click::separation::contains_element(dst->_M_ptr, 0, 4, 3));
    }
    have separate(memory(dst->_M_ptr[3]), memory(this->data[0..4])) by {
        apply(click::separation::separate_restrict(memory(dst->_M_ptr[0..4]), memory(this->data[0..4]), memory(dst->_M_ptr[3]), memory(this->data[0..4])));
    }
    step();
    step() by {
        have at(function.entry, 0u64) < at(function.entry, load<uint64>(byte_offset(dst, 8))) by {
            rewrite(at(function.entry, dst->_M_extent._M_extent_value), at(function.entry, 4u64));
            close();
        }
        close();
    }
    have call(0).result == (old(dst->_M_ptr) + 0) by {
        close();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0..4])) by {
        close();
    }
    step() by {
        close();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->data)) by {
        close();
    }
    have separate(region(2).footprint, memory(this->data)) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->data));
        };
    }
    have at(region(2).exit, this->data) == at(region(2).entry, this->data) by {
        preserve(memory(this->data), region(2));
    }
    have this->data == old(this->data) by {
        close();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->remaining)) by {
        close();
    }
    have separate(region(2).footprint, memory(this->remaining)) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(this->remaining));
        };
    }
    have at(region(2).exit, this->remaining) == at(region(2).entry, this->remaining) by {
        preserve(memory(this->remaining), region(2));
    }
    have this->remaining == old(this->remaining) by {
        close();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0])) by {
        have at(region(3).entry, separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0]))) by {
            close();
        }
        close();
    }
    have separate(region(2).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[0]));
        };
    }
    have at(region(2).exit, load<uint8>((old(this->data) + 0))) == at(region(2).entry, load<uint8>((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(2));
    }
    have load<uint8>((old(this->data) + 0)) == old(this->data[0]) by {
        close();
    }
    have load<uint8>((old(dst->_M_ptr) + 0)) == old(this->data[0]) by {
        close();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[1])) by {
        have at(region(3).entry, separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[1]))) by {
            close();
        }
        close();
    }
    have separate(region(2).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[1]));
        };
    }
    have at(region(2).exit, load<uint8>((old(this->data) + 1))) == at(region(2).entry, load<uint8>((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(2));
    }
    have load<uint8>((old(this->data) + 1)) == old(this->data[1]) by {
        close();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[2])) by {
        have at(region(3).entry, separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[2]))) by {
            close();
        }
        close();
    }
    have separate(region(2).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[2]));
        };
    }
    have at(region(2).exit, load<uint8>((old(this->data) + 2))) == at(region(2).entry, load<uint8>((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(2));
    }
    have load<uint8>((old(this->data) + 2)) == old(this->data[2]) by {
        close();
    }
    have separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[3])) by {
        have at(region(3).entry, separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[3]))) by {
            close();
        }
        close();
    }
    have separate(region(2).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(at(call(0).exit, call(0).result)[0]), memory(old(this->data)[3]));
        };
    }
    have at(region(2).exit, load<uint8>((old(this->data) + 3))) == at(region(2).entry, load<uint8>((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(2));
    }
    have load<uint8>((old(this->data) + 3)) == old(this->data[3]) by {
        close();
    }
    step();
    step() by {
        have at(function.entry, 1u64) < at(function.entry, load<uint64>(byte_offset(dst, 8))) by {
            rewrite(at(function.entry, dst->_M_extent._M_extent_value), at(function.entry, 4u64));
            close();
        }
        close();
    }
    have call(1).result == (old(dst->_M_ptr) + 1) by {
        close();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0..4])) by {
        close();
    }
    step() by {
        close();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->data)) by {
        close();
    }
    have separate(region(5).footprint, memory(this->data)) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->data));
        };
    }
    have at(region(5).exit, this->data) == at(region(5).entry, this->data) by {
        preserve(memory(this->data), region(5));
    }
    have this->data == old(this->data) by {
        close();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->remaining)) by {
        close();
    }
    have separate(region(5).footprint, memory(this->remaining)) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(this->remaining));
        };
    }
    have at(region(5).exit, this->remaining) == at(region(5).entry, this->remaining) by {
        preserve(memory(this->remaining), region(5));
    }
    have this->remaining == old(this->remaining) by {
        close();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0])) by {
        have at(region(6).entry, separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0]))) by {
            close();
        }
        close();
    }
    have separate(region(5).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[0]));
        };
    }
    have at(region(5).exit, load<uint8>((old(this->data) + 0))) == at(region(5).entry, load<uint8>((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(5));
    }
    have load<uint8>((old(this->data) + 0)) == old(this->data[0]) by {
        close();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[1])) by {
        have at(region(6).entry, separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[1]))) by {
            close();
        }
        close();
    }
    have separate(region(5).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[1]));
        };
    }
    have at(region(5).exit, load<uint8>((old(this->data) + 1))) == at(region(5).entry, load<uint8>((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(5));
    }
    have load<uint8>((old(this->data) + 1)) == old(this->data[1]) by {
        close();
    }
    have separate(memory(old(dst->_M_ptr)[1]), memory(old(dst->_M_ptr)[0])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 1, 0));
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(dst->_M_ptr)[0])) by {
        close();
    }
    have separate(region(5).footprint, memory(old(dst->_M_ptr)[0])) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(dst->_M_ptr)[0]));
        };
    }
    have at(region(5).exit, load<uint8>((old(dst->_M_ptr) + 0))) == at(region(5).entry, load<uint8>((old(dst->_M_ptr) + 0))) by {
        preserve(memory(old(dst->_M_ptr)[0]), region(5));
    }
    have load<uint8>((old(dst->_M_ptr) + 0)) == old(this->data[0]) by {
        close();
    }
    have load<uint8>((old(dst->_M_ptr) + 1)) == old(this->data[1]) by {
        close();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[2])) by {
        have at(region(6).entry, separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[2]))) by {
            close();
        }
        close();
    }
    have separate(region(5).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[2]));
        };
    }
    have at(region(5).exit, load<uint8>((old(this->data) + 2))) == at(region(5).entry, load<uint8>((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(5));
    }
    have load<uint8>((old(this->data) + 2)) == old(this->data[2]) by {
        close();
    }
    have separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[3])) by {
        have at(region(6).entry, separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[3]))) by {
            close();
        }
        close();
    }
    have separate(region(5).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(at(call(1).exit, call(1).result)[0]), memory(old(this->data)[3]));
        };
    }
    have at(region(5).exit, load<uint8>((old(this->data) + 3))) == at(region(5).entry, load<uint8>((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(5));
    }
    have load<uint8>((old(this->data) + 3)) == old(this->data[3]) by {
        close();
    }
    step();
    step() by {
        have at(function.entry, 2u64) < at(function.entry, load<uint64>(byte_offset(dst, 8))) by {
            rewrite(at(function.entry, dst->_M_extent._M_extent_value), at(function.entry, 4u64));
            close();
        }
        close();
    }
    have call(2).result == (old(dst->_M_ptr) + 2) by {
        close();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0..4])) by {
        close();
    }
    step() by {
        close();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->data)) by {
        close();
    }
    have separate(region(8).footprint, memory(this->data)) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->data));
        };
    }
    have at(region(8).exit, this->data) == at(region(8).entry, this->data) by {
        preserve(memory(this->data), region(8));
    }
    have this->data == old(this->data) by {
        close();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->remaining)) by {
        close();
    }
    have separate(region(8).footprint, memory(this->remaining)) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(this->remaining));
        };
    }
    have at(region(8).exit, this->remaining) == at(region(8).entry, this->remaining) by {
        preserve(memory(this->remaining), region(8));
    }
    have this->remaining == old(this->remaining) by {
        close();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0])) by {
        have at(region(9).entry, separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0]))) by {
            close();
        }
        close();
    }
    have separate(region(8).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[0]));
        };
    }
    have at(region(8).exit, load<uint8>((old(this->data) + 0))) == at(region(8).entry, load<uint8>((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(8));
    }
    have load<uint8>((old(this->data) + 0)) == old(this->data[0]) by {
        close();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[1])) by {
        have at(region(9).entry, separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[1]))) by {
            close();
        }
        close();
    }
    have separate(region(8).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[1]));
        };
    }
    have at(region(8).exit, load<uint8>((old(this->data) + 1))) == at(region(8).entry, load<uint8>((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(8));
    }
    have load<uint8>((old(this->data) + 1)) == old(this->data[1]) by {
        close();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[2])) by {
        have at(region(9).entry, separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[2]))) by {
            close();
        }
        close();
    }
    have separate(region(8).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[2]));
        };
    }
    have at(region(8).exit, load<uint8>((old(this->data) + 2))) == at(region(8).entry, load<uint8>((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(8));
    }
    have load<uint8>((old(this->data) + 2)) == old(this->data[2]) by {
        close();
    }
    have separate(memory(old(dst->_M_ptr)[2]), memory(old(dst->_M_ptr)[0])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 2, 0));
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(dst->_M_ptr)[0])) by {
        close();
    }
    have separate(region(8).footprint, memory(old(dst->_M_ptr)[0])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(dst->_M_ptr)[0]));
        };
    }
    have at(region(8).exit, load<uint8>((old(dst->_M_ptr) + 0))) == at(region(8).entry, load<uint8>((old(dst->_M_ptr) + 0))) by {
        preserve(memory(old(dst->_M_ptr)[0]), region(8));
    }
    have load<uint8>((old(dst->_M_ptr) + 0)) == old(this->data[0]) by {
        close();
    }
    have separate(memory(old(dst->_M_ptr)[2]), memory(old(dst->_M_ptr)[1])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 2, 1));
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(dst->_M_ptr)[1])) by {
        close();
    }
    have separate(region(8).footprint, memory(old(dst->_M_ptr)[1])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(dst->_M_ptr)[1]));
        };
    }
    have at(region(8).exit, load<uint8>((old(dst->_M_ptr) + 1))) == at(region(8).entry, load<uint8>((old(dst->_M_ptr) + 1))) by {
        preserve(memory(old(dst->_M_ptr)[1]), region(8));
    }
    have load<uint8>((old(dst->_M_ptr) + 1)) == old(this->data[1]) by {
        close();
    }
    have load<uint8>((old(dst->_M_ptr) + 2)) == old(this->data[2]) by {
        close();
    }
    have separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[3])) by {
        have at(region(9).entry, separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[3]))) by {
            close();
        }
        close();
    }
    have separate(region(8).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(at(call(2).exit, call(2).result)[0]), memory(old(this->data)[3]));
        };
    }
    have at(region(8).exit, load<uint8>((old(this->data) + 3))) == at(region(8).entry, load<uint8>((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(8));
    }
    have load<uint8>((old(this->data) + 3)) == old(this->data[3]) by {
        close();
    }
    step();
    step() by {
        have at(function.entry, 3u64) < at(function.entry, load<uint64>(byte_offset(dst, 8))) by {
            rewrite(at(function.entry, dst->_M_extent._M_extent_value), at(function.entry, 4u64));
            close();
        }
        close();
    }
    have call(3).result == (old(dst->_M_ptr) + 3) by {
        close();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0..4])) by {
        close();
    }
    step() by {
        close();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->data)) by {
        close();
    }
    have separate(region(11).footprint, memory(this->data)) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->data));
        };
    }
    have at(region(11).exit, this->data) == at(region(11).entry, this->data) by {
        preserve(memory(this->data), region(11));
    }
    have this->data == old(this->data) by {
        close();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->remaining)) by {
        close();
    }
    have separate(region(11).footprint, memory(this->remaining)) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(this->remaining));
        };
    }
    have at(region(11).exit, this->remaining) == at(region(11).entry, this->remaining) by {
        preserve(memory(this->remaining), region(11));
    }
    have this->remaining == old(this->remaining) by {
        close();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0])) by {
        have at(region(12).entry, separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0]))) by {
            close();
        }
        close();
    }
    have separate(region(11).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[0]));
        };
    }
    have at(region(11).exit, load<uint8>((old(this->data) + 0))) == at(region(11).entry, load<uint8>((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(11));
    }
    have load<uint8>((old(this->data) + 0)) == old(this->data[0]) by {
        close();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[1])) by {
        have at(region(12).entry, separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[1]))) by {
            close();
        }
        close();
    }
    have separate(region(11).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[1]));
        };
    }
    have at(region(11).exit, load<uint8>((old(this->data) + 1))) == at(region(11).entry, load<uint8>((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(11));
    }
    have load<uint8>((old(this->data) + 1)) == old(this->data[1]) by {
        close();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[2])) by {
        have at(region(12).entry, separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[2]))) by {
            close();
        }
        close();
    }
    have separate(region(11).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[2]));
        };
    }
    have at(region(11).exit, load<uint8>((old(this->data) + 2))) == at(region(11).entry, load<uint8>((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(11));
    }
    have load<uint8>((old(this->data) + 2)) == old(this->data[2]) by {
        close();
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[3])) by {
        have at(region(12).entry, separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[3]))) by {
            close();
        }
        close();
    }
    have separate(region(11).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(this->data)[3]));
        };
    }
    have at(region(11).exit, load<uint8>((old(this->data) + 3))) == at(region(11).entry, load<uint8>((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(11));
    }
    have load<uint8>((old(this->data) + 3)) == old(this->data[3]) by {
        close();
    }
    have separate(memory(old(dst->_M_ptr)[3]), memory(old(dst->_M_ptr)[0])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 3, 0));
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[0])) by {
        close();
    }
    have separate(region(11).footprint, memory(old(dst->_M_ptr)[0])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[0]));
        };
    }
    have at(region(11).exit, load<uint8>((old(dst->_M_ptr) + 0))) == at(region(11).entry, load<uint8>((old(dst->_M_ptr) + 0))) by {
        preserve(memory(old(dst->_M_ptr)[0]), region(11));
    }
    have load<uint8>((old(dst->_M_ptr) + 0)) == old(this->data[0]) by {
        close();
    }
    have separate(memory(old(dst->_M_ptr)[3]), memory(old(dst->_M_ptr)[1])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 3, 1));
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[1])) by {
        close();
    }
    have separate(region(11).footprint, memory(old(dst->_M_ptr)[1])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[1]));
        };
    }
    have at(region(11).exit, load<uint8>((old(dst->_M_ptr) + 1))) == at(region(11).entry, load<uint8>((old(dst->_M_ptr) + 1))) by {
        preserve(memory(old(dst->_M_ptr)[1]), region(11));
    }
    have load<uint8>((old(dst->_M_ptr) + 1)) == old(this->data[1]) by {
        close();
    }
    have separate(memory(old(dst->_M_ptr)[3]), memory(old(dst->_M_ptr)[2])) by {
        apply(click::separation::separate_elements(old(dst->_M_ptr), 3, 2));
    }
    have separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[2])) by {
        close();
    }
    have separate(region(11).footprint, memory(old(dst->_M_ptr)[2])) by {
        normalize() using {
            separate(memory(at(call(3).exit, call(3).result)[0]), memory(old(dst->_M_ptr)[2]));
        };
    }
    have at(region(11).exit, load<uint8>((old(dst->_M_ptr) + 2))) == at(region(11).entry, load<uint8>((old(dst->_M_ptr) + 2))) by {
        preserve(memory(old(dst->_M_ptr)[2]), region(11));
    }
    have load<uint8>((old(dst->_M_ptr) + 2)) == old(this->data[2]) by {
        close();
    }
    have load<uint8>((old(dst->_M_ptr) + 3)) == old(this->data[3]) by {
        close();
    }
    have separate(memory((this as (uint64 *))[0..1]), memory(old(this->data)[0..4])) by {
        close();
    }
    step() by {
        close();
    }
    have separate(memory((&(this->remaining))[0..1]), memory(old(this->data)[0..4])) by {
        close();
    }
    step() by {
        close();
    }
    step();
    have separate(memory(this->data), memory(old(dst->_M_ptr)[0])) by {
        close();
    }
    have separate(region(12).footprint, memory(old(dst->_M_ptr)[0])) by {
        normalize() using {
            separate(memory(this->data), memory(old(dst->_M_ptr)[0]));
        };
    }
    have at(region(12).exit, load<uint8>((old(dst->_M_ptr) + 0))) == at(region(12).entry, load<uint8>((old(dst->_M_ptr) + 0))) by {
        preserve(memory(old(dst->_M_ptr)[0]), region(12));
    }
    have at(region(12).exit, load<uint8>((old(dst->_M_ptr) + 0))) == old(this->data[0]) by {
        close();
    }
    have separate(memory(this->data), memory(old(dst->_M_ptr)[1])) by {
        close();
    }
    have separate(region(12).footprint, memory(old(dst->_M_ptr)[1])) by {
        normalize() using {
            separate(memory(this->data), memory(old(dst->_M_ptr)[1]));
        };
    }
    have at(region(12).exit, load<uint8>((old(dst->_M_ptr) + 1))) == at(region(12).entry, load<uint8>((old(dst->_M_ptr) + 1))) by {
        preserve(memory(old(dst->_M_ptr)[1]), region(12));
    }
    have at(region(12).exit, load<uint8>((old(dst->_M_ptr) + 1))) == old(this->data[1]) by {
        close();
    }
    have separate(memory(this->data), memory(old(dst->_M_ptr)[2])) by {
        close();
    }
    have separate(region(12).footprint, memory(old(dst->_M_ptr)[2])) by {
        normalize() using {
            separate(memory(this->data), memory(old(dst->_M_ptr)[2]));
        };
    }
    have at(region(12).exit, load<uint8>((old(dst->_M_ptr) + 2))) == at(region(12).entry, load<uint8>((old(dst->_M_ptr) + 2))) by {
        preserve(memory(old(dst->_M_ptr)[2]), region(12));
    }
    have at(region(12).exit, load<uint8>((old(dst->_M_ptr) + 2))) == old(this->data[2]) by {
        close();
    }
    have separate(memory(this->data), memory(old(dst->_M_ptr)[3])) by {
        close();
    }
    have separate(region(12).footprint, memory(old(dst->_M_ptr)[3])) by {
        normalize() using {
            separate(memory(this->data), memory(old(dst->_M_ptr)[3]));
        };
    }
    have at(region(12).exit, load<uint8>((old(dst->_M_ptr) + 3))) == at(region(12).entry, load<uint8>((old(dst->_M_ptr) + 3))) by {
        preserve(memory(old(dst->_M_ptr)[3]), region(12));
    }
    have at(region(12).exit, load<uint8>((old(dst->_M_ptr) + 3))) == old(this->data[3]) by {
        close();
    }
    have separate(memory(this->remaining), memory(old(dst->_M_ptr)[0])) by {
        close();
    }
    have separate(region(13).footprint, memory(old(dst->_M_ptr)[0])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(dst->_M_ptr)[0]));
        };
    }
    have at(region(13).exit, load<uint8>((old(dst->_M_ptr) + 0))) == at(region(13).entry, load<uint8>((old(dst->_M_ptr) + 0))) by {
        preserve(memory(old(dst->_M_ptr)[0]), region(13));
    }
    have at(region(13).exit, load<uint8>((old(dst->_M_ptr) + 0))) == old(this->data[0]) by {
        close();
    }
    have separate(memory(this->remaining), memory(old(dst->_M_ptr)[1])) by {
        close();
    }
    have separate(region(13).footprint, memory(old(dst->_M_ptr)[1])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(dst->_M_ptr)[1]));
        };
    }
    have at(region(13).exit, load<uint8>((old(dst->_M_ptr) + 1))) == at(region(13).entry, load<uint8>((old(dst->_M_ptr) + 1))) by {
        preserve(memory(old(dst->_M_ptr)[1]), region(13));
    }
    have at(region(13).exit, load<uint8>((old(dst->_M_ptr) + 1))) == old(this->data[1]) by {
        close();
    }
    have separate(memory(this->remaining), memory(old(dst->_M_ptr)[2])) by {
        close();
    }
    have separate(region(13).footprint, memory(old(dst->_M_ptr)[2])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(dst->_M_ptr)[2]));
        };
    }
    have at(region(13).exit, load<uint8>((old(dst->_M_ptr) + 2))) == at(region(13).entry, load<uint8>((old(dst->_M_ptr) + 2))) by {
        preserve(memory(old(dst->_M_ptr)[2]), region(13));
    }
    have at(region(13).exit, load<uint8>((old(dst->_M_ptr) + 2))) == old(this->data[2]) by {
        close();
    }
    have separate(memory(this->remaining), memory(old(dst->_M_ptr)[3])) by {
        close();
    }
    have separate(region(13).footprint, memory(old(dst->_M_ptr)[3])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(dst->_M_ptr)[3]));
        };
    }
    have at(region(13).exit, load<uint8>((old(dst->_M_ptr) + 3))) == at(region(13).entry, load<uint8>((old(dst->_M_ptr) + 3))) by {
        preserve(memory(old(dst->_M_ptr)[3]), region(13));
    }
    have at(region(13).exit, load<uint8>((old(dst->_M_ptr) + 3))) == old(this->data[3]) by {
        close();
    }
    have separate(memory(this->data), memory(old(this->data)[0])) by {
        close();
    }
    have separate(region(12).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(this->data), memory(old(this->data)[0]));
        };
    }
    have at(region(12).exit, load<uint8>((old(this->data) + 0))) == at(region(12).entry, load<uint8>((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(12));
    }
    have at(region(12).exit, load<uint8>((old(this->data) + 0))) == old(this->data[0]) by {
        close();
    }
    have separate(memory(this->data), memory(old(this->data)[1])) by {
        close();
    }
    have separate(region(12).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(this->data), memory(old(this->data)[1]));
        };
    }
    have at(region(12).exit, load<uint8>((old(this->data) + 1))) == at(region(12).entry, load<uint8>((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(12));
    }
    have at(region(12).exit, load<uint8>((old(this->data) + 1))) == old(this->data[1]) by {
        close();
    }
    have separate(memory(this->data), memory(old(this->data)[2])) by {
        close();
    }
    have separate(region(12).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(this->data), memory(old(this->data)[2]));
        };
    }
    have at(region(12).exit, load<uint8>((old(this->data) + 2))) == at(region(12).entry, load<uint8>((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(12));
    }
    have at(region(12).exit, load<uint8>((old(this->data) + 2))) == old(this->data[2]) by {
        close();
    }
    have separate(memory(this->data), memory(old(this->data)[3])) by {
        close();
    }
    have separate(region(12).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(this->data), memory(old(this->data)[3]));
        };
    }
    have at(region(12).exit, load<uint8>((old(this->data) + 3))) == at(region(12).entry, load<uint8>((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(12));
    }
    have at(region(12).exit, load<uint8>((old(this->data) + 3))) == old(this->data[3]) by {
        close();
    }
    have separate(memory(this->remaining), memory(old(this->data)[0])) by {
        close();
    }
    have separate(region(13).footprint, memory(old(this->data)[0])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(this->data)[0]));
        };
    }
    have at(region(13).exit, load<uint8>((old(this->data) + 0))) == at(region(13).entry, load<uint8>((old(this->data) + 0))) by {
        preserve(memory(old(this->data)[0]), region(13));
    }
    have at(region(13).exit, load<uint8>((old(this->data) + 0))) == old(this->data[0]) by {
        close();
    }
    have separate(memory(this->remaining), memory(old(this->data)[1])) by {
        close();
    }
    have separate(region(13).footprint, memory(old(this->data)[1])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(this->data)[1]));
        };
    }
    have at(region(13).exit, load<uint8>((old(this->data) + 1))) == at(region(13).entry, load<uint8>((old(this->data) + 1))) by {
        preserve(memory(old(this->data)[1]), region(13));
    }
    have at(region(13).exit, load<uint8>((old(this->data) + 1))) == old(this->data[1]) by {
        close();
    }
    have separate(memory(this->remaining), memory(old(this->data)[2])) by {
        close();
    }
    have separate(region(13).footprint, memory(old(this->data)[2])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(this->data)[2]));
        };
    }
    have at(region(13).exit, load<uint8>((old(this->data) + 2))) == at(region(13).entry, load<uint8>((old(this->data) + 2))) by {
        preserve(memory(old(this->data)[2]), region(13));
    }
    have at(region(13).exit, load<uint8>((old(this->data) + 2))) == old(this->data[2]) by {
        close();
    }
    have separate(memory(this->remaining), memory(old(this->data)[3])) by {
        close();
    }
    have separate(region(13).footprint, memory(old(this->data)[3])) by {
        normalize() using {
            separate(memory(this->remaining), memory(old(this->data)[3]));
        };
    }
    have at(region(13).exit, load<uint8>((old(this->data) + 3))) == at(region(13).entry, load<uint8>((old(this->data) + 3))) by {
        preserve(memory(old(this->data)[3]), region(13));
    }
    have at(region(13).exit, load<uint8>((old(this->data) + 3))) == old(this->data[3]) by {
        close();
    }
    have separate(memory(this->data), memory(this->remaining)) by {
        close();
    }
    have separate(region(12).footprint, memory(this->remaining)) by {
        normalize() using {
            separate(memory(this->data), memory(this->remaining));
        };
    }
    have at(region(12).exit, this->remaining) == at(region(12).entry, this->remaining) by {
        preserve(memory(this->remaining), region(12));
    }
    have at(region(12).exit, this->remaining) == old(this->remaining) by {
        close();
    }
    have to_integer(this->remaining) == (to_integer(old(this->remaining)) - to_integer(4u64)) by {
        have (to_integer(((at(region(12).entry, load<uint64>(byte_offset(this, 8))) - 4u64) as uint64)) : Integer) == (to_integer(old((load<uint64>(byte_offset(this, 8)) as uint64))) - 4) by {
            have 0 <= (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) - 4) by {
                have 0 <= (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) - 4) by {
                    have (-old(to_integer(this->remaining)) + at(region(12).exit, to_integer(this->remaining))) == 0 by {
                        have at(region(12).exit, to_integer(this->remaining)) == old(to_integer(this->remaining)) by {
                            close();
                        }
                        have (at(region(12).exit, to_integer(this->remaining)) - old(to_integer(this->remaining))) == 0 by {
                            apply(click::integer::equal_difference(at(region(12).exit, to_integer(this->remaining)), old(to_integer(this->remaining))));
                        }
                        have (-old(to_integer(this->remaining)) + at(region(12).exit, to_integer(this->remaining))) == (at(region(12).exit, to_integer(this->remaining)) - old(to_integer(this->remaining))) by {
                            close();
                        }
                        apply(click::integer::equal_substitute((at(region(12).exit, to_integer(this->remaining)) - old(to_integer(this->remaining))), 0, (-old(to_integer(this->remaining)) + at(region(12).exit, to_integer(this->remaining))), 0));
                    }
                    have (old(to_integer(this->remaining)) + -at(region(12).exit, to_integer(this->remaining))) <= 0 by {
                        have -(-old(to_integer(this->remaining)) + at(region(12).exit, to_integer(this->remaining))) == -(0 : Integer) by {
                            apply(click::integer::equal_negate((-old(to_integer(this->remaining)) + at(region(12).exit, to_integer(this->remaining))), 0));
                        }
                        have (old(to_integer(this->remaining)) + -at(region(12).exit, to_integer(this->remaining))) == 0 by {
                            have (old(to_integer(this->remaining)) + -at(region(12).exit, to_integer(this->remaining))) == -(-old(to_integer(this->remaining)) + at(region(12).exit, to_integer(this->remaining))) by {
                                close();
                            }
                            have 0 == -(0 : Integer) by {
                                close();
                            }
                            apply(click::integer::equal_substitute(-(-old(to_integer(this->remaining)) + at(region(12).exit, to_integer(this->remaining))), -(0 : Integer), (old(to_integer(this->remaining)) + -at(region(12).exit, to_integer(this->remaining))), 0));
                        }
                        apply(click::integer::equal_le((old(to_integer(this->remaining)) + -at(region(12).exit, to_integer(this->remaining))), 0));
                    }
                    have (-old(to_integer(this->remaining)) + 4) <= 0 by {
                        have 4 <= at(function.entry, to_integer(this->remaining)) by {
                            close();
                        }
                        have (-old(to_integer(this->remaining)) + 4) == (4 - at(function.entry, to_integer(this->remaining))) by {
                            close();
                        }
                        apply(click::integer::le_difference(4, at(function.entry, to_integer(this->remaining)), (-old(to_integer(this->remaining)) + 4)));
                    }
                    have (-at(region(12).exit, to_integer(this->remaining)) + 4) <= 0 by {
                        have (old(to_integer(this->remaining)) + -at(region(12).exit, to_integer(this->remaining)) + (-old(to_integer(this->remaining)) + 4)) <= (0 + 0) by {
                            apply(click::integer::add_le((old(to_integer(this->remaining)) + -at(region(12).exit, to_integer(this->remaining))), 0, (-old(to_integer(this->remaining)) + 4), 0));
                        }
                        have (-at(region(12).exit, to_integer(this->remaining)) + 4) == (old(to_integer(this->remaining)) + -at(region(12).exit, to_integer(this->remaining)) + (-old(to_integer(this->remaining)) + 4)) by {
                            close();
                        }
                        have (0 : Integer) == (0 + 0) by {
                            close();
                        }
                        apply(click::integer::le_substitute((old(to_integer(this->remaining)) + -at(region(12).exit, to_integer(this->remaining)) + (-old(to_integer(this->remaining)) + 4)), (0 + 0), (-at(region(12).exit, to_integer(this->remaining)) + 4), 0));
                    }
                    have (-at(region(12).exit, to_integer(this->remaining)) + 4) == (0 - (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) - 4)) by {
                        close();
                    }
                    apply(click::integer::difference_le(0, (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) - 4), (-at(region(12).exit, to_integer(this->remaining)) + 4)));
                }
                close();
            }
            have (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) - 4) <= 18446744073709551615 by {
                have (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) - 4) <= 18446744073709551615 by {
                    have (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551615) <= 0 by {
                        have to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) <= 18446744073709551615 by {
                            close();
                        }
                        have to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) <= to_integer(18446744073709551615u64) by {
                            close();
                        }
                        have (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551615) == (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) - to_integer(18446744073709551615u64)) by {
                            close();
                        }
                        apply(click::integer::le_difference(to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))), to_integer(18446744073709551615u64), (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551615)));
                    }
                    have (-4 : Integer) <= 0 by {
                        close();
                    }
                    have (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551619) <= 0 by {
                        have (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551615 + -4) <= (0 + 0) by {
                            apply(click::integer::add_le((to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551615), 0, -4, 0));
                        }
                        have (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551619) == (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551615 + -4) by {
                            close();
                        }
                        have (0 : Integer) == (0 + 0) by {
                            close();
                        }
                        apply(click::integer::le_substitute((to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551615 + -4), (0 + 0), (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551619), 0));
                    }
                    have (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551619) == ((to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) - 4) - 18446744073709551615) by {
                        close();
                    }
                    apply(click::integer::difference_le((to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) - 4), 18446744073709551615, (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) + -18446744073709551619)));
                }
                close();
            }
            have (to_integer(((at(region(12).entry, load<uint64>(byte_offset(this, 8))) - 4u64) as uint64)) : Integer) == (to_integer(at(region(12).entry, load<uint64>(byte_offset(this, 8)))) - 4) by {
                close();
            }
            close();
        }
        close();
    }
    close();
    have dst->_M_ptr[0] == old(this->data[0]) by {
        close();
    }
    have dst->_M_ptr[1] == old(this->data[1]) by {
        close();
    }
    have dst->_M_ptr[2] == old(this->data[2]) by {
        close();
    }
    have dst->_M_ptr[3] == old(this->data[3]) by {
        close();
    }
    have this->data == (old(this->data) + 4) by {
        close();
    }
    have to_integer(this->remaining) == (to_integer(old(this->remaining)) - to_integer(4u64)) by {
        close();
    }
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
}

uint32 le32toh_internal(uint32 little_endian_32bits) {
    ensures result == little_endian_32bits by {
        step();
        step();
        have result == little_endian_32bits by {
            close();
        }
        close();
        close();
        close();
        close();
    }
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
    step();
    step();
    step();
    step();
    step();
    step();
    have call(1).parameter(__sp)._M_extent._M_extent_value == 1u64 by {
        close();
    }
    have call(1).parameter(__sp)._M_ptr == &obj by {
        close();
    }
    have to_integer(call(1).result._M_extent._M_extent_value) == (to_integer(call(1).parameter(__sp)._M_extent._M_extent_value) * to_integer(4u64)) by {
        close();
    }
    have call(1).result._M_extent._M_extent_value == 4u64 by {
        rewrite(to_integer(call(1).result._M_extent._M_extent_value), (to_integer(call(1).parameter(__sp)._M_extent._M_extent_value) * to_integer(4u64)));
        rewrite(call(1).parameter(__sp)._M_extent._M_extent_value, 1u64);
        close();
    }
    have call(1).result._M_ptr == (&obj as (uint8 *)) by {
        close();
    }
    step();
    step() {
        requires call(2).parameter(dst)._M_extent._M_extent_value == 4u64 by {
            close();
        }
        requires 4u64 <= s.remaining by {
            close();
        }
        requires separate(memory(at(call(2).entry, call(2).parameter(dst)._M_ptr)[0..4]), memory(s.data[0..4])) by {
            transport(at(function.entry, separate(memory(at(call(2).entry, call(2).parameter(dst)._M_ptr)[0..4]), memory(s.data[0..4]))), separate(memory(at(call(2).entry, call(2).parameter(dst)._M_ptr)[0..4]), memory(s.data[0..4]))) using {
                at(function.entry, separate(memory(at(call(2).entry,
                    call(2).parameter(dst)._M_ptr)[0..4]), memory(s.data[0..4])));
            };
        }
        requires separate(memory(at(call(2).entry, load<uint8*>(region(4).result))[0..4]), memory(s.data[0..4])) by {
            close();
        }
        requires separate(memory((&s as (int32 *))[0..2]), memory((s.data as (uint8 *))[0..4])) by {
            close();
        }
        requires separate(memory((&s as (uint64 *))[1..2]), memory((s.data as (uint8 *))[0..4])) by {
            close();
        }
    }
    have call(2).parameter(dst)._M_ptr == (&obj as (uint8 *)) by {
        close();
    }
    have (&obj as (uint8 *))[0] == 120u8 by {
        close();
    }
    have (&obj as (uint8 *))[1] == 86u8 by {
        close();
    }
    have (&obj as (uint8 *))[2] == 52u8 by {
        close();
    }
    have (&obj as (uint8 *))[3] == 18u8 by {
        close();
    }
    have obj == 305419896u32 by {
        close();
    }
    step();
    step();
    step();
    close();
    have result == 305419896u32 by {
        close();
    }
    have s.data == (old(s.data) + 4) by {
        close();
    }
    have to_integer(s.remaining) == (to_integer(old(s.remaining)) - to_integer(4u64)) by {
        close();
    }
    close();
    close();
    close();
    close();
    close();
    close();
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
} by {
    step() {
        requires 4u64 <= stream.remaining by {
            close();
        }
        requires stream.data[0] == 120u8 by {
            close();
        }
        requires stream.data[1] == 86u8 by {
            close();
        }
        requires stream.data[2] == 52u8 by {
            close();
        }
        requires stream.data[3] == 18u8 by {
            close();
        }
        requires separate(memory((&stream as (int32 *))[0..2]), memory((stream.data as (uint8 *))[0..4])) by {
            close();
        }
        requires separate(memory((&stream as (uint64 *))[1..2]), memory((stream.data as (uint8 *))[0..4])) by {
            close();
        }
    }
    step();
    have result == 305419896u32 by {
        close();
    }
    have stream.data == (old(stream.data) + 4) by {
        close();
    }
    have to_integer(stream.remaining) == (to_integer(old(stream.remaining)) - to_integer(4u64)) by {
        close();
    }
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
}
