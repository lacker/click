/* The hosted stream handle has an opaque, incomplete pointee type. */
#pragma once
#include <stddef.h>
typedef struct __click_c_stdio_FILE FILE;
extern FILE *const __click_c_stdio_stdout;
#define stdout ((FILE *)__click_c_stdio_stdout)

int printf(const char *format, ...);
int fprintf(FILE *stream, const char *format, ...);
int snprintf(char *buffer, size_t size, const char *format, ...);
