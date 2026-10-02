verifying "arrays.rs";

void Guard_drop(struct Guard* self) {
    requires separate(memory(object(self)), memory(self->slot[0..1]));
    owns &self->slot;
    owns self->saved;
    owns self->slot[0..1];
    ensures self->slot == old(self->slot);
    ensures self->saved == old(self->saved);
    ensures self->slot[0] == old(self->saved);
} by { execute(); simp(); }

uint32 guarded_array(int32* value, uint16 x) {
    owns value[0..1];
    ensures result == x;
    ensures value[0] == old(value[0]);
} by { execute(); simp(); }

uint8 large_array() {
    ensures result == 7;
} by { execute(); simp(); }

uint8 increment(int32* value) {
    requires value[0] < 2147483647;
    owns value[0..1];
    ensures result == 7;
    ensures value[0] == old(value[0]) + 1;
} by { execute(); simp(); }

void empty_array(int32* value) {
    requires value[0] < 2147483647;
    owns value[0..1];
    ensures value[0] == old(value[0]) + 1;
} by { execute(); simp(); }

uint32 explicit_array() {
    ensures result == 9;
} by { execute(); simp(); }

uint8 cast_array(uint32 x) {
    requires x == 257;
    ensures result == 1;
} by { execute(); simp(); }
