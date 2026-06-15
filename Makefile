SHELL := /usr/bin/env bash

LEAN_FILE ?= Autobahn.lean
MODEL_NAME ?= $(basename $(notdir $(LEAN_FILE)))
BUILD_DIR ?= .lake/model_checker_builds/$(MODEL_NAME)
OUT_DIR ?= model-check-output
TIMEOUT ?= 300s

CVC5_DYLIB ?= .lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so
LEAN_CC_WRAPPER ?= $(abspath tools/lean-cc-host-glibc.sh)
LEAN_PATH_VALUE = $(shell lake env printenv LEAN_PATH)
LEAN_WITH_CVC5 = env LEAN_CC="$(LEAN_CC_WRAPPER)" lake env lean --load-dynlib=$(CVC5_DYLIB)
RESULT_JSON ?= $(OUT_DIR)/$(MODEL_NAME)-result.json
PROGRESS_NDJSON ?= $(OUT_DIR)/$(MODEL_NAME)-progress.ndjson

.PHONY: help elaborate compile-model run-model-check model-check clean-model-output

help:
	@printf '%s\n' 'Targets:'
	@printf '%s\n' '  make elaborate LEAN_FILE=Autobahn.lean'
	@printf '%s\n' '      Run lake env lean on the source file. If #model_check compiled is enabled,'
	@printf '%s\n' '      this also asks Veil to generate .lake/model_checker_builds/<model>.'
	@printf '%s\n' '  make compile-model LEAN_FILE=Autobahn.lean'
	@printf '%s\n' '      Compile .lake/model_checker_builds/<model>/Model.lean to Model.olean.'
	@printf '%s\n' '  make run-model-check LEAN_FILE=Autobahn.lean'
	@printf '%s\n' '      Run .lake/model_checker_builds/<model>/ModelCheckerMain.lean and save JSON/NDJSON.'
	@printf '%s\n' '  make model-check LEAN_FILE=Autobahn.lean'
	@printf '%s\n' '      Run elaborate, compile-model, and run-model-check.'
	@printf '%s\n' ''
	@printf '%s\n' 'Useful variables:'
	@printf '%s\n' '  TIMEOUT=300s'
	@printf '%s\n' '  CVC5_DYLIB=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so'
	@printf '%s\n' '  LEAN_CC_WRAPPER=tools/lean-cc-host-glibc.sh'
	@printf '%s\n' '  RESULT_JSON=model-check-output/<model>-result.json'
	@printf '%s\n' '  PROGRESS_NDJSON=model-check-output/<model>-progress.ndjson'

elaborate:
	$(LEAN_WITH_CVC5) $(LEAN_FILE)

compile-model:
	test -f "$(BUILD_DIR)/Model.lean"
	cd "$(BUILD_DIR)" && LEAN_PATH=".:$(LEAN_PATH_VALUE)" lean --load-dynlib "$(abspath $(CVC5_DYLIB))" -o Model.olean Model.lean

run-model-check:
	test -f "$(BUILD_DIR)/ModelCheckerMain.lean"
	mkdir -p "$(OUT_DIR)"
	cd "$(BUILD_DIR)" && timeout "$(TIMEOUT)" bash -c 'tail -f /dev/null | env LEAN_PATH=".:$(LEAN_PATH_VALUE)" lean --load-dynlib "$(abspath $(CVC5_DYLIB))" --run ModelCheckerMain.lean > "$(abspath $(RESULT_JSON))" 2> "$(abspath $(PROGRESS_NDJSON))"'

model-check: elaborate compile-model run-model-check

clean-model-output:
	rm -f "$(RESULT_JSON)" "$(PROGRESS_NDJSON)"
