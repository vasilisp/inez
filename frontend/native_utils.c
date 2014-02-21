#define NULL (void*)0

typedef struct { unsigned char data[16]; } IID;

IID IID_IUnknown = { { 0, 0, 0, 0, 0, 0, 0, 0,
		       0, 0, 0, 0, 0, 0, 0, 0x80 } };

void* scip_null_cons()
{
	return NULL;
}

void* scip_null_sol()
{
	return NULL;
}
