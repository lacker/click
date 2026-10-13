verifying "label_copy.c";

extern uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
}

uint64 label_measure(const char* src) {
    requires cstr_readable(src);
    ensures result < 32;
} by {
    execute();
    simp();
}
