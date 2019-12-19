PLSETTINGS	:= pl.conf
CLIQUERBASE     := ../cliquer-1.21

all: $(PLSETTINGS)
	gcc -O4 -I $(PLBASE)/include -I $(CLIQUERBASE) $(PLCFLAGS) $(PLLDFLAGS) -fPIC -shared -c pl-cliquer.c
	gcc -O4 -I $(PLBASE)/include -I $(CLIQUERBASE) $(PLCFLAGS) $(PLLDFLAGS) -fPIC -shared -o pl-cliquer.so \
	pl-cliquer.o $(CLIQUERBASE)/cliquer.o $(CLIQUERBASE)/graph.o $(CLIQUERBASE)/reorder.o

clean:
	rm -f *.o *.so $(PLSETTINGS)

$(PLSETTINGS):	
	swipl -dump-runtime-variables | sed s/\"//g |  sed s/\;//g > pl.conf

-include $(PLSETTINGS)

.PHONY: all cliquer clean
