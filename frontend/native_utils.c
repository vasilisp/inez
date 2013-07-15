#include "caml/mlvalues.h"

typedef struct { unsigned char data[16]; } IID;

IID IID_IUnknown = { { 0, 0, 0, 0, 0, 0, 0, 0,
		       0, 0, 0, 0, 0, 0, 0, 0x80 } };

void* scip_null_cons()
{
	return NULL;
}
