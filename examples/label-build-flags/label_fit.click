verifying "label_fit.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
} by {
    execute();
    have result <= length by auto;
    simp();
}
