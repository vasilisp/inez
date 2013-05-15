/* super ugly hack to fix a compile failure; I don't know what I am
   doing */

typedef struct { unsigned char data[16]; } IID;

IID IID_IUnknown = { { 0, 0, 0, 0, 0, 0, 0, 0,
		       0, 0, 0, 0, 0, 0, 0, 0x80 } };
