TARGET = parOMP3
SHELL  = /bin/sh

DBGFLAGS   = -g -Wall
CFLAGS     = -g -O3 -Wall -fno-strict-aliasing -fomit-frame-pointer
EXTRACFLAGS= -fopenmp
#CFLAGS    = $(DBGFLAGS)

# Various linkers use different flags to force static compilation. Choose
# the one which is relevant for your installation.
#
# Solaris ld (global)
#STATIC    = -dn

# Solaris ld (toggle: no shared object accepted until -B dynamic is seen
#STATIC    = -B static

# gcc
#STATIC    = -static

CC         = /usr/bin/g++
CPPFLAGS   = -I. -I/usr/local/include
LD         = /usr/bin/gcc
LDFLAGS    = -g -O3 -Wall -fno-strict-aliasing -fomit-frame-pointer    -Wl,--export-dynamic 
MODLD      = /usr/bin/gcc
MODLDFLAGS = -shared  $(CFLAGS) $(DLCFLAGS) -Wl,-shared 
EXTRAMODLDFLAGS = -lc -lm -L/usr/local/lib -lpari
EXTRALIBS  = 

RUNPTH     = -Wl,-rpath "/usr/local/lib"
DLCFLAGS   = -fPIC
LIBS       = -lm -L/usr/local/lib -lpari

RM = rm -f


OBJS = $(TARGET).o
DYN = lib$(TARGET).so
ALL = $(TARGET)-sta $(TARGET)-dyn $(DYN)

dft: $(TARGET)-dyn

all: $(ALL)

sta: $(TARGET)-sta

dyn: $(TARGET)-dyn

dynlib: $(DYN)

$(DYN): $(OBJS)
	$(MODLD) -o $@ $(MODLDFLAGS) $(EXTRACFLAGS) $(OBJS) $(EXTRAMODLDFLAGS)

$(TARGET)-sta: $(OBJS)
	$(LD) -o $@ $(LDFLAGS) $(EXTRACFLAGS) $< $(EXTRALIBS) $(STATIC) $(LIBS)

$(TARGET)-dyn: $(OBJS)
	$(LD) -g -o $@ $(LDFLAGS) $(EXTRACFLAGS) $< $(EXTRALIBS) $(RUNPTH) $(LIBS)

%.o: %.c
	$(CC) -g -c $(CFLAGS) $(EXTRACFLAGS) $(CPPFLAGS) $(DLCFLAGS) $<
clean:
	-$(RM) *.o $(ALL)
gen:
	make TARGET=$(TARGET) EXTRALIBS=-lpthread
