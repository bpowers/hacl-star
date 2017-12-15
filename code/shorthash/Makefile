include ../../Makefile.include

# Files for verification
SHORTHASH_FILES= \
	Hacl.Impl.Shorthash.SipHash24.fst \
	Hacl.Shorthash.SipHash24.fst

FSTAR_INCLUDES+=--include ../hash

# Parameter for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)

ct: $(addsuffix -lax, $(SHORTHASH_FILES))
hints: $(addsuffix .hints, $(SHORTHASH_FILES))
verify: $(addsuffix -verify, $(SHORTHASH_FILES))
all-ct: ct
all-ver: verify
all-ci: verify
all-hints: hints

extract-c: shorthash-c/Hacl_Shorthash_SipHash24.c

test: test-shorthash_siphash24.exe

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf shorthash-c

# Common call to Kremlin for both extraction and tests
KREMLIN_ARGS+= \
		-verbose -tmpdir shorthash-c \
		-I $(HACL_HOME)/code/hash \
		-drop Prims \
		-drop Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
		-drop 'Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create,Spec.*,Hacl.Impl.SHA2_256.*' \
		-bundle "Hacl.Shorthash.SipHash24=Hacl.Impl.Shorthash.SipHash24,Hacl.Shorthash.SipHash24" \
		-ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 \
		$(KREMLIN_TESTLIB)

shorthash-c/out.krml: Hacl.Shorthash.SipHash24.fst Hacl.Test.Shorthash.SipHash24.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-translation -no-prefix Hacl.Shorthash.SipHash24 \
		$^ -o $@

shorthash-c/Hacl_Shorthash_SipHash24.c: shorthash-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation -no-prefix Hacl.Shorthash.SipHash24 \
		$^ -o $@

test-shorthash_siphash24.exe: shorthash-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -no-prefix Hacl.Test.Shorthash.SipHash24 \
		$^ -o $@
	./$@
