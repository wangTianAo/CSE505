# 
# ###############################################
# make variables
# ###############################################
# 

# cliquer settings
CLIQUERBASE   	:= cliquer-1.21

#
# ###############################################
# compile all sources
# ###############################################
#

all: $(CLIQUERBASE) pl-cliquer

pl-cliquer:
	(cd src && make all)

install: uninstall
	mkdir build
	cp src/pl-cliquer.so build
	cp src/plcliquer.pl  build

uninstall:
	rm -rf build

.PHONY: all pl-cliquer install uninstall

#
# ###############################################
# clean-*
# ###############################################
#

clean: clean-cliquer clean-plcliquer

clean-plcliquer:
	(cd src && make clean)


clean-cliquer: clean-$(CLIQUERBASE)

clean-$(CLIQUERBASE):
	rm -rf $(CLIQUERBASE)

.PHONY: clean clean-settings clean-plcliquer clean-cliquer clean-$(CLIQUERBASE)

# 
# ###############################################
# cliquer
# ###############################################
# 

cliquer: $(CLIQUERBASE)

$(CLIQUERBASE): clean-$(CLIQUERBASE) FORCE
	(cd cliquer ;		\
	 tar xvf $@.tar.gz ;	\
	 mv $@ ..)
	(cd $@; make CFLAGS=-fPIC -j)

FORCE:

.PHONY: cliquer FORCE
