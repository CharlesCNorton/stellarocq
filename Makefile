# Stellarocq: proofs -> extraction -> patched OCaml -> checker binary.
#
# Needs the opam switch described in README.md active, and COQRUN_STUBS
# pointing at rocq-runtime's C stubs archive if it is not at the default
# opam location.

OPAM_SWITCH ?= stellarocq
OPAM_LIB    := $(shell opam var lib --switch=$(OPAM_SWITCH) 2>/dev/null)
KERNEL      := $(OPAM_LIB)/rocq-runtime/kernel
export COQRUN_STUBS ?= $(OPAM_LIB)/rocq-runtime/vm/libcoqrun_stubs.a

# What the trust base names. A switch that differs is not the one the audit
# was run against, so the checker refuses to claim its numbers.
EXPECT := rocq-core:9.1.1 coq-stdlib:9.2.0 coq-interval:4.11.4 \
          coq-flocq:4.2.2 coq-coquelicot:3.4.5 \
          coq-mathcomp-ssreflect:2.4.0 ocaml:4.14.2

.PHONY: all proofs extract checker audit versions clean

versions:
	@opam list --switch=$(OPAM_SWITCH) --installed --short --columns=name,version > .versions.tmp 2>/dev/null; \
	ok=1; \
	for pv in $(EXPECT); do \
	  p=$${pv%%:*}; want=$${pv##*:}; \
	  got=$$(awk -v p="$$p" '$$1==p {print $$2; exit}' .versions.tmp); \
	  if [ "$$got" = "$$want" ]; then \
	    printf '  ok   %-24s %s\n' "$$p" "$$got"; \
	  else \
	    printf '  DIFF %-24s installed %s, trust base names %s\n' "$$p" "$${got:-absent}" "$$want"; ok=0; \
	  fi; \
	done; \
	rm -f .versions.tmp; \
	[ $$ok = 1 ] || { echo "the switch differs from the one the audit was run against"; exit 1; }

all: checker

proofs: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

extract: proofs
	mkdir -p extract
	cd extract && rm -f *.ml *.mli && \
	rocq compile -R ../theories Stellarocq ../theories/Extract.v
	cp $(KERNEL)/uint63.ml $(KERNEL)/float64.ml \
	   $(KERNEL)/float64_common.ml extract/
	python3 gen/patch_extract.py extract
	cp driver/main.ml driver/dune driver/dune-project extract/

checker: extract
	cd extract && dune build ./main.exe
	@echo "checker: extract/_build/default/main.exe"

audit: proofs
	rocq compile -R theories Stellarocq theories/Audit.v

clean:
	$(MAKE) -f Makefile.coq clean 2>/dev/null || true
	rm -f Makefile.coq Makefile.coq.conf
	cd extract && rm -rf _build *.ml *.mli *.vo *.glob
