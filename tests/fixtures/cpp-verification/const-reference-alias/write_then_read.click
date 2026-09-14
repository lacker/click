verifying "write_then_read.cpp";

int32 write_then_read(int32* writable, const int32* readable) {
    requires writable == readable;
    owns writable[0..1];
    ensures result == 7;
    ensures writable[0] == 7;
} by {
    execute();
    simp();
}
