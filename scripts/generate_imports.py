#!/usr/bin/env python3
"""Keep the aggregate library import equal to the entire owned source inventory.

This does not establish that a module builds. Use --check after `lake build`
to confirm aggregate coverage; the Lean build and axiom audit are separate.
"""
from pathlib import Path
import argparse
import re

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true', help='check without writing')
args = parser.parse_args()
files = sorted((root / 'IndependentSetDiscovery').rglob('*.lean'))
modules = [p.relative_to(root).with_suffix('').as_posix().replace('/', '.') for p in files]
for path in files:
    if re.search(r'^import\s+IndependentSetDiscovery\s*$', path.read_text(), re.M):
        raise SystemExit(f'Aggregate import cycle in {path.relative_to(root)}')
expected = ''.join(f'import {name}\n' for name in modules)
aggregate = root / 'IndependentSetDiscovery.lean'
if args.check:
    if aggregate.read_text() != expected:
        existing = set(re.findall(r'^import\s+(\S+)', aggregate.read_text(), re.M))
        missing = [m for m in modules if m not in existing]
        extra = sorted(existing - set(modules))
        raise SystemExit(f'Aggregate inventory mismatch. Missing: {missing}; extra: {extra}')
    print(f'Aggregate covers all {len(modules)} owned Lean modules.')
else:
    aggregate.write_text(expected)
    print(f'Wrote aggregate imports for {len(modules)} owned Lean modules.')
