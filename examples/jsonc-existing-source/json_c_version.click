// The C and upstream header are unchanged. This proof uses Click's default
// x86_64-linux-userspace target (eight-bit signed plain char).
verifying "json_c_version.c";

const char *json_c_version() {
    ensures readable: viewable(result[0..5]);
    ensures first: result[0] == '0';
    ensures dot: result[1] == '.';
    ensures major_digit: result[2] == '1';
    ensures minor_digit: result[3] == '7';
    ensures terminator: result[4] == '\0';
} by {
    execute();
    simp();
}

int json_c_version_num() {
    ensures result == 4352;
} by {
    execute();
    simp();
}
