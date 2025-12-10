# Makefile for Rocq Transformer Implementation
# Uses `rocq makefile` to generate build rules

.PHONY: all clean help

# Default target: generate Makefile.coq and build all modules
all: Makefile.coq
	$(MAKE) -f Makefile.coq all

# Generate Makefile.coq from _CoqProject
Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

# Clean all generated files
clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

# Pattern rule for individual .vo file compilation
%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq $@

# Pattern rule for individual .vos file compilation (quick)
%.vos: Makefile.coq
	$(MAKE) -f Makefile.coq $@

# Help target
help:
	@echo "Rocq Transformer Makefile"
	@echo ""
	@echo "Available targets:"
	@echo "  make all              - Compile all .v files"
	@echo "  make clean            - Remove all compiled files"
	@echo "  make <module>.vo      - Compile specific module"
	@echo "  make <module>.vos     - Quick compile specific module"
	@echo ""
	@echo "Example:"
	@echo "  make Transformer/Tensor.vo"
	@echo "  make Transformer/Config.vo"
