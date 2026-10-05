#!/usr/bin/env bash
# Run the local reproducible checks. Full logs stay in ignored .cache/checks/.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .cache/checks

run() {
  local label="$1"
  shift
  printf 'Checking %s ... ' "$label"
  if "$@" > ".cache/checks/$label.txt" 2>&1; then
    printf 'PASS\n'
  else
    printf 'FAIL\n' >&2
    cat ".cache/checks/$label.txt" >&2
    exit 1
  fi
}

run inventory python3 scripts/generate_imports.py --check
run source-hygiene python3 scripts/check_release.py
run build lake build
for test in Tests/*.lean; do
  run "test-$(basename "$test" .lean)" lake env lean --run "$test"
done
for test in scripts/Smoke*.lean; do
  run "smoke-$(basename "$test" .lean)" lake env lean "$test"
done
run statement-contracts bash scripts/check_statement_contracts.sh
run kernel-audit lake env lean scripts/release_audit.lean
grep 'RELEASE_AUDIT_PASS' .cache/checks/kernel-audit.txt
printf 'All local checks passed. See comparator/README.md for the official comparator status.\n'
