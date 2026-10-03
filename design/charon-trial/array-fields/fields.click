verifying "fields.rs";
uint32 read(const struct Lanes* state, uint64 index) {
    requires index < 4u64;
    views state->values[0..4];
    ensures result == old(state->values[(int32)(uint32)index]);
} by { execute(); simp(); }
void write(struct Lanes* state, uint64 index, uint32 value) {
    requires index == 1u64;
    owns state->values[0..4];
    views state->marker;
    ensures state->values[(int32)(uint32)index] == value;
    ensures state->values[0] == old(state->values[0]);
    ensures state->values[2] == old(state->values[2]);
    ensures state->values[3] == old(state->values[3]);
    ensures state->marker == old(state->marker);
} by {
    have ((int32)(uint32)index) == 1 by { rewrite(index == 1u64); simp(); }
    execute(); simp();
}
uint32 array_first(const uint32* values) {
    views values[0..4];
    ensures result == old(values[0]);
} by { execute(); simp(); }
uint32 borrowed_first(const struct Lanes* state) {
    views state->values[0..4];
    ensures result == old(state->values[0]);
} by { execute(); simp(); }
uint32 tuple_read(const struct Words* state, uint64 index) {
    requires index < 4u64;
    views state->_0[0..4];
    ensures result == old(state->_0[(int32)(uint32)index]);
} by { execute(); simp(); }
uint8 byte_read(const struct Bytes* state, uint64 index) {
    requires index < 7u64;
    views (state->bytes)[0..7];
    ensures result == old(state->bytes[(int32)(uint32)index]);
} by { execute(); simp(); }
uint8 slice_first(const uint8* bytes, uint64 bytes_len) {
    requires bytes_len > 0u64;
    requires bytes_len <= 2147483647u64;
    views bytes[0..(int32)(uint32)bytes_len];
    ensures result == old(bytes[0]);
} by { execute(); simp(); }
uint8 borrowed_byte(const struct Bytes* state) {
    views (state->bytes)[0..7];
    ensures result == old(state->bytes[0]);
} by { execute(); simp(); }
uint64 empty_len(const struct Empty* state) {
    ensures result == 0u64;
} by { execute(); simp(); }
