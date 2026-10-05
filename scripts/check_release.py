#!/usr/bin/env python3
"""Inventory owned Lean sources and reject obvious unfinished proof commands.

This is a conservative source hygiene check, not a kernel or semantic audit.
Run the pinned Lean build and declaration-dependency axiom audit separately.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def code_only(text):
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        c = text[i]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: out.append('\n' if c == '\n' else ' '); i += 1
        elif string:
            if c == '\\': out.extend('  '); i += 2
            else:
                if c == '"': string = False
                out.append('\n' if c == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            j = text.find('\n', i)
            if j < 0: break
            out.extend(' ' * (j-i)); i = j
        elif c == '"': string = True; out.append(' '); i += 1
        else: out.append(c); i += 1
    return ''.join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    files = sorted((root / 'IndependentSetDiscovery').rglob('*.lean'))
    files += [root / 'IndependentSetDiscovery.lean']
    challenge = root / 'StatementContracts/Challenge.lean'
    files += sorted(p for p in (root / 'StatementContracts').rglob('*.lean') if p != challenge)
    files += [root / 'StatementContracts.lean']
    files += sorted((root / 'Tests').rglob('*.lean'))
    files += sorted((root / 'scripts').rglob('*.lean'))
    inventory, findings = [], []
    for path in files:
        data = path.read_bytes()
        text = data.decode('utf-8')
        rel = path.relative_to(root).as_posix()
        inventory.append({'path': rel, 'sha256': hashlib.sha256(data).hexdigest(),
                          'lines': len(text.splitlines()), 'bytes': len(data)})
        stripped = code_only(text)
        for match in re.finditer(r'\b(sorry|admit|axiom|sorryAx|unsafe)\b', stripped):
            findings.append({'path': rel, 'token': match.group(),
                             'line': stripped.count('\n', 0, match.start()) + 1})
    result = {'scope': 'Owned Lean source hygiene only; no semantic or kernel assurance',
              'exclusion': 'StatementContracts/Challenge.lean: isolated untrusted statement placeholders',
              'files': inventory, 'findings': findings,
              'source_hygiene_pass': not findings}
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    else: print(rendered, end='')
    return bool(findings)


if __name__ == '__main__':
    raise SystemExit(main())
