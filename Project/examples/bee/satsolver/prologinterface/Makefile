-include SETTINGS

CC=g++
SWI_HOME=$(PLBASE)
SWI_LIBDIR= -L$(SWI_HOME)/lib/$(PLARCH)
MINISATBASE=../glucose-2.2
FLAGS= -Wno-unused-result
DFLAGS= -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS

all: clean compile

compile:
	$(CC) $(FLAGS) $(DFLAGS) -O3 -fomit-frame-pointer -s -shared -fpic -o pl-glucose.so pl-glucose.cpp \
	$(MINISATBASE)/core/Solver.cc \
	$(SWI_LIBDIR) \
	-I $(SWI_HOME)/include \
	-I $(MINISATBASE)/ \
	-I $(MINISATBASE)/core

clean:
	rm -f *.so

createTar:
	(cd .. ; tar -cvzf plGlucose_src.tar.gz prologinterface glucose-2.2)
