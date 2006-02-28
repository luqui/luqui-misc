CFLAGS = -O
LDLIBS = -lpapi 

all: normal prefetch prefetch_concat concat

normal: fpdiv.c
	gcc $(CFLAGS) -o $@ $< $(LDLIBS)

prefetch: fpdiv.c
	gcc $(CFLAGS) -DPREFETCH -o $@ $< $(LDLIBS)

prefetch_concat: fpdiv.c
	gcc $(CFLAGS) -DCONCAT -DPREFETCH -o $@ $< $(LDLIBS)

concat: fpdiv.c
	gcc $(CFLAGS) -DCONCAT -o $@ $< $(LDLIBS)
