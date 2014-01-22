extern void init(char plain[8], char cipher[8], char iv[8],
                 char key[8], int kbits);
extern int doit(void);
extern int selftest(void);
extern void gethash(unsigned long *hash1p, unsigned long *hash2p);
