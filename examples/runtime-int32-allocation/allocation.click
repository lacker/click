resource allocated_int32s(data: int32*, count: int32) {
    contains allocation(data, count * 4);
    owns data[0..count];
    fact data != 0;
}

resource maybe_allocated_int32s(data: int32*, count: int32) {
    if data != 0 {
        contains allocation(data, count * 4);
        owns data[0..count];
    }
}

verifying "allocate_int32s.c";
verifying "free_int32s.c";

int32* allocate_int32s(int32 count) {
    requires 1 <= count;
    requires count <= 536870911;
    produces maybe_allocated_int32s(result, count);
} by {
    execute();
    fold(maybe_allocated_int32s(result, count));
    simp();
}

int32 free_int32s(int32 data[], int32 count) {
    requires 1 <= count;
    requires data != 0;
    consumes allocated_int32s(data, count);
    ensures result == 0;
} by {
    unfold(allocated_int32s(data, count));
    execute();
    simp();
}
