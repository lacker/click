verifying "bump_reference.cpp";

int32 bump_pointer(int32* pointer) {
    requires pointer[0] < 2147483647;
    owns pointer[0..1];
    ensures pointer[0] == old(pointer[0]) + 1;
    ensures result == pointer[0];
} by {
    execute();
    simp();
}

int32 bump_reference(int32* value) {
    requires value[0] < 2147483647;
    owns value[0..1];
    ensures value[0] == old(value[0]) + 1;
    ensures result == value[0];
} by {
    execute();
    simp();
}
