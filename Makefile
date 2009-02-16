include ./template.mk
FOLKUNG=Folkung
FOLKUNGTGZ=folkung3.tar.gz
MINISAT=$(FOLKUNG)/minisat/current-base
MINISAT_INST=Folkung/instantiate


all: build doc_haskell

build: build_minisat build_haskell

install: install_minisat install_haskell

uninstall: uninstall_minisat unregister_haskell

clean: clean_minisat clean_haskell

prepare: 
	tar xvzf $(FOLKUNGTGZ)

.PHONY: clean

######################################################################
###  minisat stuff
######################################################################

install_minisat: build_minisat
	install -m 644 $(MINISAT)/libminisat.a $(PREFIX)/lib
	install -m 644 $(MINISAT_INST)/libinstantiate.a $(PREFIX)/lib

uninstall_minisat:
	rm $(PREFIX)/lib/libminisat.a
	rm $(PREFIX)/lib/libinstantiate.a

build_minisat: 
	make libminisat.a -C $(MINISAT) 
	make libinstantiate.a -C $(MINISAT_INST) 

clean_minisat:
	make clean -C $(MINISAT) 
	make clean -C $(MINISAT_INST) 