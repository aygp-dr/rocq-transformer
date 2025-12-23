# Makefile for Rocq Transformer Implementation
# Uses `rocq makefile` to generate build rules (falls back to coq_makefile)

.PHONY: all clean help check-rocq

# Detect rocq or coq_makefile
ROCQ_MAKEFILE := $(shell command -v rocq 2>/dev/null && echo "rocq makefile" || (command -v coq_makefile 2>/dev/null && echo "coq_makefile"))

# Default target: generate Makefile.coq and build all modules
all: check-rocq Makefile.coq
	$(MAKE) -f Makefile.coq all

# Check that rocq/coq is available
check-rocq:
ifndef ROCQ_MAKEFILE
	$(error Neither 'rocq' nor 'coq_makefile' found. Install Rocq 9.1+ via: nix develop)
endif

# Generate Makefile.coq from _CoqProject
Makefile.coq: _CoqProject
	$(ROCQ_MAKEFILE) -f _CoqProject -o Makefile.coq

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
