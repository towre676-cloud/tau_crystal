# Minimal fast path for Go — customize
.PHONY: ci-fast
ci-fast:
	@echo "[fast] go: $(CURDIR)"
	@if command -v go >/dev/null 2>&1; then \
	  P=$$(command -v nproc >/dev/null 2>&1 && nproc || sysctl -n hw.ncpu 2>/dev/null || echo 2); \
	  go test ./... -count=1 -parallel=$$P; \
	else echo "[warn] go not found; skipping"; fi
