#ifndef CONTEXT_H
#define CONTEXT_H

static inline BASE_TYPE from_header(void)
{
#if defined(__CHAR_UNSIGNED__) && VARIANT == 1
    return RESCAN(SYSTEM_VALUE);
#else
    return 7;
#endif
}

#endif
