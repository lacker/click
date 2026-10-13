#include "label_config.h"
#include "label.h"

/* The longest label that fits a LABEL_CAPACITY buffer with its NUL. */
unsigned long label_fit(unsigned long length)
{
	if (length >= LABEL_CAPACITY)
		return LABEL_CAPACITY - 1;
	return length;
}
