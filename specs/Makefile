# Makefile for TLA+ specification verification

# TLA+ tools location (adjust if needed)
TLC = tlc

# Specifications
SPECS = LodeMining LodeEmissions HashrateMarket

.PHONY: all clean check-% check-all help

help:
	@echo "TLA+ Specification Verification"
	@echo "================================"
	@echo ""
	@echo "Available targets:"
	@echo "  make check-all         - Verify all specifications"
	@echo "  make check-LodeMining  - Verify LodeMining specification"
	@echo "  make check-LodeEmissions - Verify LodeEmissions specification"
	@echo "  make check-HashrateMarket - Verify HashrateMarket specification"
	@echo "  make clean             - Remove generated files"
	@echo ""
	@echo "Requirements:"
	@echo "  - TLA+ tools installed (brew install tlaplus)"
	@echo "  - Or use TLA+ Toolbox GUI"

all: check-all

check-all: $(addprefix check-,$(SPECS))

check-%:
	@echo "Verifying $* specification..."
	@$(TLC) $*.tla -config $*.cfg -workers auto
	@echo "✓ $* verification complete"
	@echo ""

clean:
	@echo "Cleaning generated files..."
	@rm -rf states/
	@rm -f *.out
	@rm -f *.dot
	@rm -f MC.tla MC.cfg
	@echo "✓ Clean complete"

# Individual targets
check-mining: check-LodeMining
check-emissions: check-LodeEmissions
check-market: check-HashrateMarket
