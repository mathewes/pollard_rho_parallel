TARGET = parOMP3
SHELL  = /bin/sh

DBGFLAGS   = -g -Wall
CFLAGS     = -g -O3 -Wall -fno-strict-aliasing -fomit-frame-pointer
EXTRACFLAGS= -fopenmp

CC         = /usr/bin/gcc
CPPFLAGS   = -I. -I/usr/local/include
LD         = /usr/bin/gcc
LDFLAGS    = -g -O3 -Wall -fno-strict-aliasing -fomit-frame-pointer    -Wl,--export-dynamic 
MODLD      = /usr/bin/gcc
MODLDFLAGS = -shared  $(CFLAGS) $(DLCFLAGS) -Wl,-shared 
EXTRAMODLDFLAGS = -lc -lm -L/usr/local/lib -lpari

RUNPTH     = -Wl,-rpath "/usr/local/lib"
DLCFLAGS   = -fPIC
LIBS       = -lm -L/usr/local/lib -lpari

RM = rm -f

OBJS = $(TARGET).o
DYN = lib$(TARGET).so
ALL = $(TARGET)-sta $(TARGET)-dyn $(DYN)

dft: $(TARGET)-dyn

$(TARGET)-dyn: $(OBJS)
	$(LD) -g -o $@ $(LDFLAGS) $(EXTRACFLAGS) $< $(RUNPTH) $(LIBS)

%.o: %.c
	$(CC) -g -c $(CFLAGS) $(EXTRACFLAGS) $(CPPFLAGS) $(DLCFLAGS) $<
clean:
	-$(RM) *.o $(ALL)
