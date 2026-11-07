# The C runtime of openverse.
#
#   make          build/cverse
#   make asan     build/cverse-asan (AddressSanitizer + UndefinedBehaviorSanitizer)
#   make test     unit tests, tests/core/*.vbc against the Lean binary (both
#                 builds), and a mutation fuzz smoke test under the sanitizers
#
# LEAN names the Lean reference binary; FUZZ_N the number of fuzz mutants.

CC       ?= cc
CFLAGS   := -std=c11 -Wall -Wextra -Werror -O2
SANFLAGS := -fsanitize=address,undefined -fno-sanitize-recover=all -fno-omit-frame-pointer -g
CPPFLAGS := -Iinclude
B        := build
ROOT     := ..
LEAN     ?= $(ROOT)/.lake/build/bin/openverse
CORE     := $(ROOT)/tests/core
FUZZ_N   ?= 5000
FUZZ_SEED ?= 1

LIBSRC   := src/arith.c src/store.c src/load.c src/value.c src/objects.c src/prims.c src/floats.c src/interp.c
OBJ      := $(LIBSRC:src/%.c=$(B)/obj/%.o)
OBJ_SAN  := $(LIBSRC:src/%.c=$(B)/obj-san/%.o)
TESTS    := test_arith test_store test_load test_interp
TESTBIN  := $(TESTS:%=$(B)/%) $(B)/fuzz_smoke

.PHONY: all asan test unit core fuzz clean
.SECONDARY:
all: $(B)/cverse
asan: $(B)/cverse-asan

$(B)/obj/%.o: src/%.c | $(B)/obj
	$(CC) $(CPPFLAGS) $(CFLAGS) -MMD -MP -c $< -o $@
$(B)/obj-san/%.o: src/%.c | $(B)/obj-san
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SANFLAGS) -MMD -MP -c $< -o $@
$(B)/obj/main.o: src/main.c | $(B)/obj
	$(CC) $(CPPFLAGS) $(CFLAGS) -pthread -MMD -MP -c $< -o $@
$(B)/obj-san/main.o: src/main.c | $(B)/obj-san
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SANFLAGS) -DVX_MAIN_DEPTH=4000000u -pthread -MMD -MP -c $< -o $@
$(B)/obj-san/%.o: tests/%.c | $(B)/obj-san
	$(CC) $(CPPFLAGS) $(CFLAGS) $(SANFLAGS) -MMD -MP -c $< -o $@

$(B)/cverse: $(OBJ) $(B)/obj/main.o
	$(CC) $(CFLAGS) -pthread -o $@ $^ -lm
$(B)/cverse-asan: $(OBJ_SAN) $(B)/obj-san/main.o
	$(CC) $(CFLAGS) $(SANFLAGS) -pthread -o $@ $^ -lm

# Unit tests and the fuzz driver link the library objects, sanitized.
$(B)/test_%: $(B)/obj-san/test_%.o $(OBJ_SAN)
	$(CC) $(CFLAGS) $(SANFLAGS) -o $@ $^ -lm
$(B)/fuzz_smoke: $(B)/obj-san/fuzz_smoke.o $(OBJ_SAN)
	$(CC) $(CFLAGS) $(SANFLAGS) -o $@ $^ -lm

$(B)/obj $(B)/obj-san:
	mkdir -p $@

test: unit core fuzz

unit: $(TESTS:%=$(B)/%)
	@for t in $(TESTS); do echo "== $$t"; $(B)/$$t $(CORE) || exit 1; done

core: $(B)/cverse $(B)/cverse-asan
	@sh tests/run_core.sh $(B)/cverse $(LEAN) $(CORE) $(B)/core
	@sh tests/run_core.sh $(B)/cverse-asan $(LEAN) $(CORE) $(B)/core-asan

fuzz: $(B)/fuzz_smoke
	@echo "== fuzz_smoke ($(FUZZ_N) mutants)"
	@$(B)/fuzz_smoke $(FUZZ_N) $(FUZZ_SEED) $(CORE)/*.vbc

clean:
	rm -rf $(B)

-include $(wildcard $(B)/obj/*.d $(B)/obj-san/*.d)
