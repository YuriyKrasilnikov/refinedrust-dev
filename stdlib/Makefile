STDLIB = sized index mem clone num closures result option ptr arithops ptr_advanced controlflow alloc rr_internal boxed cmp range iterator vec rwlock atomic spin stdlib
#btreemap

RUST_TARGET ?= $(shell rustc -vV | sed -n 's|host: ||p')
RUST_PATH ?=	target/$(RUST_TARGET)/release




generate_stdlib: $(STDLIB:=.crate)

#clean_stdlib: $(STDLIB:=.clean)
clean_stdlib:
	@for dir in $(shell find . -mindepth 1 -maxdepth 1 -type d -print); do \
		(cd $$dir && cargo clean); \
	done

stdlib.proof: generate_stdlib
	dune build --display short

%.proof:	%.crate
	cd $* && dune build --display short

%.crate:	export PATH := $(CURDIR)/../rr_frontend/$(RUST_PATH):$(PATH)
%.crate: %
	cd $* && cargo refinedrust

%.clean: phony
	cd $* && cargo clean
.PHONY: phony
