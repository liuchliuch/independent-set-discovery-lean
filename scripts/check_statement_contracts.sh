#!/usr/bin/env bash
# Local trusted-source gate; not the official sandboxed Comparator executable.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
work="$(mktemp -d "$root/.lake/statement-contracts.XXXXXX")"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/ContractNegative"
# These modules have identical theorem names, but are loaded in separate environments.
lake build StatementContracts.Challenge StatementContracts.Solution > "$work/build.log" 2>&1 || {
  cat "$work/build.log"; exit 1;
}
lake env lean --run scripts/CompareStatements.lean comparator/config.json \
  StatementContracts.Challenge StatementContracts.Solution
python3 - "$work" <<'PY'
from pathlib import Path
import sys
work=Path(sys.argv[1]); original=Path('StatementContracts/Solution.lean').read_text()
start=original.index('theorem paper_1_2\n'); end=original.index('\n/-- Lemma 3.1:', start)
first=original[start:end]
# Strengthen only a hypothesis: its ordinary Lean proof remains valid.
extra=first.replace('(hd : 2 ≤ d)', '(hd : 2 ≤ d) (_extraPremise : 100 ≤ d)', 1)
assert extra != first
(work/'ContractNegative/ExtraPremise.lean').write_text(original[:start]+extra+original[end:])
# Valid Lean proof of the wrong (weaker) proposition. The comparison must reject it.
weaker='theorem paper_1_2 : True := by\n  trivial\n'
(work/'ContractNegative/WrongConclusion.lean').write_text(original[:start]+weaker+original[end:])
# Exact right proposition, wrong trust: challenge placeholders as a fake solution.
(work/'ContractNegative/PlaceholderProof.lean').write_text(Path('StatementContracts/Challenge.lean').read_text())
PY
# lake env normally resets LEAN_PATH; compose the temporary module prefix inside it.
for name in ExtraPremise WrongConclusion PlaceholderProof; do
  lake env lean -o "$work/ContractNegative/$name.olean" "$work/ContractNegative/$name.lean" \
    > "$work/$name.compile.log" 2>&1 || { cat "$work/$name.compile.log"; exit 1; }
  if lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; shift; lean --run "$@"' \
      _ "$work" scripts/CompareStatements.lean comparator/config.json \
      StatementContracts.Challenge "ContractNegative.$name" > "$work/$name.check.log" 2>&1; then
    echo "NEGATIVE_CONTROL_FAILED: accepted $name" >&2; exit 1
  fi
  case "$name" in
    PlaceholderProof) expected='UNEXPECTED_AXIOMS ISDContracts.paper_1_2';;
    *) expected='STATEMENT_MISMATCH ISDContracts.paper_1_2';;
  esac
  grep -F "$expected" "$work/$name.check.log" >/dev/null || {
    echo "Wrong failure for $name:" >&2; cat "$work/$name.check.log"; exit 1;
  }
  echo "LOCAL_NEGATIVE_CONTROL_PASS $name: compiled, then rejected by $expected"
done
echo 'LOCAL_STATEMENT_CONTRACT_GATE_PASS: 16 paper contracts and 3 negative controls'
