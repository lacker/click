#include <string.h>
#include "label.h"

/* How many bytes of src label_copy keeps. */
unsigned long label_measure(const char *src)
{
	return label_fit(strlen(src));
}

/* Copy src into a LABEL_CAPACITY buffer, truncating, and terminate it. */
unsigned long label_copy(char *dst, const char *src)
{
	unsigned long n = label_fit(strlen(src));

	memcpy(dst, src, n);
	dst[n] = '\0';
	return n;
}
