#!/usr/bin/env python3
"""Cosmetic cleanup after pruning: drop empty namespace blocks, squeeze blank lines.
Generated certificate files (subdirectories, Small*, PackedSmall*, NineShell*, TwoOuterTableData) are untouched."""
import re, sys
from pathlib import Path
import json
root = Path(sys.argv[1]); changed = []
pruned = set(json.load(open(root/'provenance/pruning-report.json'))['removed_declarations'])
skip = re.compile(r'^(Small\d+|PackedSmall\d+|NineShellCertificate|NineShellData|TwoOuterTableData)$')
filler = r'(?:[ \t]*|open .*|open scoped .*|variable .*|set_option [^\n]* in|)'
pat = re.compile(r'^namespace (\S+)\n(?:' + filler + r'\n)*end \1[ \t]*\n?', re.M)
for p in sorted(root.glob('LRX/*.lean')) + sorted(root.glob('Research/CayleyPy/*.lean')) + [root/'GraphBridge.lean', root/'GraphLower.lean', root/'Reachability.lean']:
    if skip.match(p.stem): continue
    mod = '.'.join(p.relative_to(root).with_suffix('').parts)
    if mod not in pruned: continue
    t = p.read_text(); u = t
    # never remove the only namespace of a file that still declares something elsewhere: pattern only matches empty blocks
    u = pat.sub('', u)
    u = re.sub(r'\n{3,}', '\n\n', u)
    u = u.rstrip('\n') + '\n'
    if u != t:
        p.write_text(u); changed.append(str(p.relative_to(root)))
print(len(changed)); print('\n'.join(changed[:20]))
