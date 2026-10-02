verifying "slices.rs";
uint64 length(const uint8* bytes, uint64 bytes_len) {
    ensures result == bytes_len;
} by { execute(); simp(); }
uint8 read(const uint8* bytes, uint64 bytes_len, uint64 index) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    views bytes[0..(int32)(uint32)bytes_len];
    ensures result == old(bytes[(int32)(uint32)index]);
} by { execute(); simp(); }
void write(uint8* bytes, uint64 bytes_len, uint64 index, uint8 value) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    owns bytes[0..(int32)(uint32)bytes_len];
    ensures bytes[(int32)(uint32)index] == value;
} by { execute(); simp(); }
uint8 alias(uint8* bytes, uint64 bytes_len, uint64 index) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    owns bytes[0..(int32)(uint32)bytes_len];
    ensures result == old(bytes[(int32)(uint32)index]);
} by { execute(); simp(); }

uint8 write_read(uint8* bytes, uint64 bytes_len, uint64 index, uint8 value) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    owns bytes[0..(int32)(uint32)bytes_len];
    ensures result == value;
    ensures bytes[(int32)(uint32)index] == value;
} by { execute(); simp(); }

void Guard_drop(struct Guard* self) {
    requires separate(memory(object(self)), memory(self->slot[0..1]));
    owns &self->slot;
    owns self->saved;
    owns self->slot[0..1];
    ensures self->slot == old(self->slot);
    ensures self->saved == old(self->saved);
    ensures self->slot[0] == old(self->saved);
} by { execute(); simp(); }

uint32 guarded_read(int32* value, const uint8* bytes, uint64 bytes_len, uint64 index) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    requires separate(memory(value[0..1]), memory(bytes[0..(int32)(uint32)bytes_len]));
    owns value[0..1];
    views bytes[0..(int32)(uint32)bytes_len];
    ensures result == old((uint32)bytes[(int32)(uint32)index]);
    ensures value[0] == old(value[0]);
} by {
    execute();
    have index <= 2147483647u64 by { simp() using { index < bytes_len; bytes_len <= 2147483647u64; } }
    have 0 <= (int32)(uint32)index by { simp() using { index <= 2147483647u64; } }
    have ((int32)(uint32)index) < (int32)(uint32)bytes_len by { simp() using { index < bytes_len; bytes_len <= 2147483647u64; } }
    simp();
}
