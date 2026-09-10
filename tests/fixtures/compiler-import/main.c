#include <configured.h>

#define BASE_TYPE int
#define SUM5(a, b, c, d, e) ((a) + (b) + (c) + (d) + (e))
#define RESCAN(value) SUM5(value, 2, 3, 4, 5)
#define JOIN_INNER(a, b) a ## b
#define JOIN(a, b) JOIN_INNER(a, b)

#include "context.h"

int JOIN(ans, wer)(void)
{
    return from_header();
}
