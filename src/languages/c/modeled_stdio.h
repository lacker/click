/* The hosted stream handle has an opaque, incomplete pointee type. */
#pragma once
typedef struct __click_c_stdio_FILE FILE;
extern FILE *const __click_c_stdio_stdout;
#define stdout ((FILE *)__click_c_stdio_stdout)
