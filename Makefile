# Convenience targets mirroring the CI gate (.github/workflows/build.yml).

.PHONY: build audit test lint ci clean

build:
	lake build

# Re-run the root `#print axioms` audit lines.
audit:
	lake env lean CausalMohawkBridge.lean

# The correspondence module's `#eval main` runs during `lake build`; this is an
# explicit alias so `make test` is not a no-op.
test: build

lint:
	python3 scripts/lint_vacuous_claims.py

ci: build audit lint

clean:
	lake clean
