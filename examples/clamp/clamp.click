verifying "clamp.c";

int32 clamp(int32 x, int32 lo, int32 hi) {
    requires lo <= hi;
    ensures lo <= result and result <= hi;
    ensures lo <= x and x <= hi implies result == x;
} by auto;
