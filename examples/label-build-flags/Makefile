CPPFLAGS = -Iinclude -DLABEL_CAPACITY=32
CFLAGS = -std=c11 -O2 -Wall -Wextra

liblabel.a: label_fit.o label_copy.o
	$(AR) rcs $@ $^

label_fit.o label_copy.o: label.h
label_fit.o: include/label_config.h

clean:
	rm -f liblabel.a *.o
