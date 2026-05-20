CC ?= cc
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -Wpedantic
CPPFLAGS += -Iinclude -Isrc
LDFLAGS ?=

CORE_SRC := \
	src/lexer.c \
	src/parser.c \
	src/policy.c \
	src/syscall.c \
	src/lower.c \
	src/branch.c \
	src/validate.c \
	src/encode.c \
	src/dump.c \
	src/interp.c \
	src/syscalls.gen.c

MORDANT_SRC := src/main.c $(CORE_SRC)
MORDANT_OBJ := $(MORDANT_SRC:.c=.o)
CORE_OBJ := $(CORE_SRC:.c=.o)
TOOL_OBJ := tools/install.o tools/loader.o

AGDA ?= agda
AGDA_STDLIB ?= /home/rack/nocturne/.deps/agda-stdlib-2.3/src
AGDA_FLAGS := --no-libraries -i $(AGDA_STDLIB) -i agda

.PHONY: all clean test test-unit test-kernel agda agda-diff diff check

all: mordant mordant-load

mordant: $(MORDANT_OBJ)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(MORDANT_OBJ)

mordant-load: $(TOOL_OBJ) $(CORE_OBJ)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(TOOL_OBJ) $(CORE_OBJ)

src/syscalls.gen.c src/syscalls.gen.h: tools/gen_syscalls.sh
	sh tools/gen_syscalls.sh src/syscalls.gen.c src/syscalls.gen.h

%.o: %.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -c -o $@ $<

test-unit: mordant tests/test_mordant
	./tests/test_mordant

tests/test_mordant: tests/test_mordant.c $(CORE_SRC)
	$(CC) $(CFLAGS) $(CPPFLAGS) -o $@ tests/test_mordant.c $(CORE_SRC)

tests/kernel_test: tests/kernel_test.c tools/install.o $(CORE_SRC)
	$(CC) $(CFLAGS) $(CPPFLAGS) -o $@ tests/kernel_test.c tools/install.o $(CORE_SRC)

test-kernel: mordant tests/kernel_test
	sh tests/run_kernel_tests.sh

agda:
	$(AGDA) $(AGDA_FLAGS) agda/Mordant/Correctness.agda

tests/diff_gen: tests/diff_gen.c $(CORE_SRC)
	mkdir -p build
	$(CC) $(CFLAGS) $(CPPFLAGS) -o $@ tests/diff_gen.c $(CORE_SRC)

DIFF_N ?= 200

diff: mordant tests/diff_gen
	tests/diff_gen $(DIFF_N) build
	$(MAKE) agda-diff
	python3 tests/compare_diff.py build/c_diff.txt build/agda_diff.txt

agda-diff:
	$(AGDA) --compile $(AGDA_FLAGS) -i build agda/Mordant/RunDiff.agda
	./agda/RunDiff > build/agda_diff.txt

test: test-unit

check: all test

clean:
	rm -f $(MORDANT_OBJ) $(CORE_OBJ) tools/*.o tests/test_mordant tests/kernel_test tests/diff_gen
	rm -rf MAlonzo build agda/_build agda/MAlonzo
	rm -f mordant mordant-load agda/RunDiff
