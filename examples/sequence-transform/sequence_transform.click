verifying "sequence_transform.c";

void sequence_copy3(int32 destination[], int32 source[]) {
    owns destination[0..3];
    views source[0..3];
    requires separate(memory(destination[0..3]), memory(source[0..3]));
    mutable destination[0..3];

    ensures [destination[0], destination[1], destination[2]]
        == old([source[0], source[1], source[2]]);
} by {
    execute();
    frame();
    simp();
}

void sequence_concatenate2(
    int32 destination[],
    int32 left[],
    int32 right[]
) {
    owns destination[0..4];
    views left[0..2];
    views right[0..2];
    requires separate(memory(destination[0..4]), memory(left[0..2]));
    requires separate(memory(destination[0..4]), memory(right[0..2]));
    mutable destination[0..4];

    ensures [destination[0], destination[1]]
            ++ [destination[2], destination[3]]
        == old([left[0], left[1]] ++ [right[0], right[1]]);
} by {
    execute();
    frame();
    simp();
}

void sequence_reverse3(int32 values[]) {
    owns values[0..3];
    mutable values[0..3];

    ensures [values[0], values[1], values[2]]
        == old([values[2], values[1], values[0]]);
} by {
    execute();
    frame();
    simp();
}
