#!/usr/bin/env python3
"""Reject sorry/admit/native_decide/axiom/unsafe/implemented_by/extern in Lean code (comments and strings stripped)."""
import re, sys
from pathlib import Path

def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
            out.append('""'); i = j + 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)

bad = re.compile(r'\b(sorry|admit|native_decide|implemented_by|extern|axiom|unsafe)\b', re.M)
root = Path(sys.argv[1] if len(sys.argv) > 1 else '.')
hits = 0; files = 0; challenge_holes = 0
for p in sorted(root.rglob('*.lean')):
    if '.lake' in p.parts: continue
    files += 1
    for m in bad.finditer(strip(p.read_text())):
        if p.resolve() == (root / 'Challenge.lean').resolve() and m.group(0).strip() == 'sorry':
            challenge_holes += 1; continue
        hits += 1; print(f'{p}: {m.group(0).strip()}')
if (root / 'Challenge.lean').exists() and challenge_holes != 2:
    hits += 1; print(f'Expected exactly two Challenge placeholders, found {challenge_holes}')
print(f'checked {files} files, {hits} forbidden tokens')
sys.exit(1 if hits else 0)
