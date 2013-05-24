#include "caml/mlvalues.h"

typedef struct { unsigned char data[16]; } IID;

IID IID_IUnknown = { { 0, 0, 0, 0, 0, 0, 0, 0,
		       0, 0, 0, 0, 0, 0, 0, 0x80 } };

value address_of_value(value v)
{
	return (Val_long(((unsigned long)v) / sizeof(long)));
}
