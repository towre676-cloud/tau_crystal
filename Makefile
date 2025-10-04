.PHONY: validate structure semantic hashes

structure:
	@./scripts/ci/validate_certificates.sh

semantic:
	@python3 scripts/ci/semantic_check.py

hashes:
	@python3 scripts/ci/hash_check.py

validate: structure semantic hashes
	@echo "=== All checks passed ==="
