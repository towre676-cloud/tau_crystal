SHELL := /bin/bash
.PHONY: all build run test

all: run test

run:
	@echo ">> RUN: orchestration placeholder (Dockerized pipeline recommended)"

test:
	@echo ">> TEST: call scripts/arith/tests.sage (scaffold)"

