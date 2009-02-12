FOLKUNG=Folkung
FOLKUNGTGZ=folkung3.tar.gz
MINISAT=$(FOLKUNG)/minisat/current-base
MINISAT_INST=Folkung/instantiate
PREFIX=/usr/local
LIBS=libs
SETUP=./Setup.lhs

all: build

configure: *.cabal Setup.*
	$(SETUP) configure --prefix=$(PREFIX)

build: configure 
	$(SETUP) build

install: install_minisat build
	$(SETUP) install

install_minisat: minisat
	install -m 644 -o root $(MINISAT)/libminisat.a $(PREFIX)/lib
	install -m 644 -o root $(MINISAT_INST)/libinstantiate.a $(PREFIX)/lib
	ldconfig

uninstall_minisat:
	rm $(PREFIX)/lib/libminisat.a
	rm $(PREFIX)/lib/libinstantiate.a

minisat: 
	make libminisat.a -C $(MINISAT) 
	make libinstantiate.a -C $(MINISAT_INST) 

prepare: 
	tar xvzf $(FOLKUNGTGZ)

upload:
	./upload.sh

clean: 
	$(SETUP) clean
	make clean -C $(MINISAT) 
	make clean -C $(MINISAT_INST) 

.PHONY: clean