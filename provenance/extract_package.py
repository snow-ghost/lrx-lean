#!/usr/bin/env python3
"""Build the pruned publication Lean project for LRX.exact_diameter_all.

Usage: extract_package.py <out-dir> <work-dir> <original-repo>
Inputs (work-dir): used.tsv (dependency closure constants), ranges.tsv
(declaration ranges of all project constants), mods.txt (import closure).
Extra keep list: keep_extra.txt (constant names to keep although unused,
e.g. rfl-lemmas needed by dsimp); filled iteratively after build failures.
"""
import collections, hashlib, json, os, re, shutil, sys
from pathlib import Path

S = Path(sys.argv[2] if len(sys.argv) > 2 else '.')    # used.tsv, ranges.tsv, closure_mods.txt
SRC = Path(sys.argv[3] if len(sys.argv) > 3 else '.')  # original repository root
DST = Path(sys.argv[1])

used_consts = set(); used_mods = set()
for l in open(S/'used.tsv'):
    m, k, n = l.rstrip('\n').split('\t'); used_consts.add(n); used_mods.add(m)
closure = set(open(S/'closure_mods.txt').read().split())
keep_extra = set()
if (S/'keep_extra.txt').exists():
    keep_extra = {x.strip() for x in open(S/'keep_extra.txt') if x.strip()}
keep_mods_extra = set()
if (S/'keep_mods_extra.txt').exists():
    keep_mods_extra = {x.strip() for x in open(S/'keep_mods_extra.txt') if x.strip()}
kept = (used_mods | keep_mods_extra) & closure

def path_of(m): return m.replace('.', '/') + '.lean'

def imports_of(m):
    out = []
    for line in (SRC/path_of(m)).read_text().splitlines():
        mm = re.match(r'\s*import\s+(.*)', line)
        if mm: out += mm.group(1).split()
    return out

memo = {}
def expand(m):
    """Kept modules reachable from m through dropped modules only."""
    if m in kept or m not in closure: return {m}
    if m in memo: return memo[m]
    r = set()
    for i in imports_of(m): r |= expand(i)
    memo[m] = r; return r

# generated / certificate files are copied byte-for-byte
def protected(m):
    p = path_of(m)
    if p.count('/') >= 2 and p.startswith('LRX/'): return True
    base = Path(p).stem
    return bool(re.fullmatch(r'Small\d+|PackedSmall\d+|NineShellCertificate|NineShellData|TwoOuterTableData', base))

ranges = collections.defaultdict(list)  # module -> [(l0,c0,l1,c1,name,kind,simp)]
for l in open(S/'ranges.tsv'):
    m, n, k, l0, c0, l1, c1, simp = l.rstrip('\n').split('\t')
    ranges[m].append((int(l0), int(c0), int(l1), int(c1), n, k, simp == 'true'))

def overlaps(a, b):
    return not ((a[2], a[3]) <= (b[0], b[1]) or (b[2], b[3]) <= (a[0], a[1]))

report = {'modules_in_import_closure': len(closure), 'modules_kept': len(kept),
          'modules_dropped': sorted(closure - kept), 'removed_declarations': {}}
if DST.exists():
    for sub in ['LRX', 'Research', 'GraphBridge.lean', 'GraphLower.lean', 'Reachability.lean']:
        p = DST/sub
        if p.is_dir(): shutil.rmtree(p)
        elif p.exists(): p.unlink()
removed_names = set()
provenance = []
for m in sorted(kept):
    src = SRC/path_of(m)
    text = src.read_text()
    lines = text.split('\n')
    # 1. rewire imports
    new_lines = []
    for line in lines:
        mm = re.match(r'(\s*)import\s+(.*)', line)
        if mm:
            tgt = []
            for i in mm.group(2).split():
                for j in sorted(expand(i)):
                    if j not in tgt: tgt.append(j)
            for j in tgt:
                new_lines.append(f'{mm.group(1)}import {j}')
            continue
        new_lines.append(line)
    import_shift = len(new_lines) - len(lines)  # imports are at the top
    lines = new_lines
    removed_here = []
    if not protected(m):
        rs = ranges.get(m, [])
        live = [r for r in rs if r[4] in used_consts or r[4] in keep_extra or r[6]]
        dead = [r for r in rs if r not in live]
        dead = [r for r in dead if not any(overlaps(r, x) for x in live)]
        # merge identical ranges (structures with several constants)
        raw = sorted({(r[0], r[1], r[2], r[3]) for r in dead})
        # merge nested / overlapping spans into maximal intervals
        spans = []
        for sp in raw:
            if spans and (sp[0], sp[1]) < (spans[-1][2], spans[-1][3]):
                last = spans[-1]
                end = max((last[2], last[3]), (sp[2], sp[3]))
                spans[-1] = (last[0], last[1], end[0], end[1])
            else:
                spans.append(sp)
        names_by_span = collections.defaultdict(list)
        for r in dead:
            for sp in spans:
                if (sp[0], sp[1]) <= (r[0], r[1]) and (r[2], r[3]) <= (sp[2], sp[3]):
                    names_by_span[sp].append(r[4]); break
        # delete from bottom to top; lines are 1-based, shifted by import rewiring
        for (l0, c0, l1, c1) in sorted(spans, reverse=True):
            a, b = l0 - 1 + import_shift, l1 - 1 + import_shift
            head = lines[a][:c0]; tail = lines[b][c1:]
            # drop a dangling `open ... in` immediately preceding
            # drop dangling command prefixes `open/omit/set_option/include/variable ... in`
            while head.strip() == '':
                k = a - 1
                while k >= 0 and lines[k].strip() == '': k -= 1
                if k >= 0 and re.match(r'\s*(open|omit|set_option|include|variable|attribute|local|scoped)\b.*\bin\s*$', lines[k]):
                    a = k
                else:
                    break
            # drop a plain `/- ... -/` comment that directly precedes the declaration
            if head.strip() == '':
                k = a - 1
                while k >= 0 and lines[k].strip() == '': k -= 1
                if k >= 0 and lines[k].rstrip().endswith('-/'):
                    j = k
                    while j >= 0 and '/-' not in lines[j]: j -= 1
                    if j >= 0 and re.match(r'\s*/-(?![-!])', lines[j]) and lines[j].lstrip().startswith('/-'):
                        a = j
            repl = []
            if head.strip(): repl.append(head)
            if tail.strip(): repl.append(tail)
            lines[a:b+1] = repl
            removed_here += names_by_span[(l0, c0, l1, c1)]
        removed_names |= set(removed_here)
    out = '\n'.join(lines)
    provenance.append({'module': m, 'source': str(src.relative_to(SRC)),
                       'source_sha256': hashlib.sha256(text.encode()).hexdigest(),
                       'pruned': bool(removed_here), 'protected': protected(m)})
    if removed_here: report['removed_declarations'][m] = sorted(removed_here)
    dst = DST/path_of(m); dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(out)

# 2. drop #print axioms / #check lines that mention removed names
def short_forms(n):
    parts = n.split('.')
    return {'.'.join(parts[i:]) for i in range(len(parts))}
removed_short = set()
for n in removed_names:
    if n.startswith('_private'): n = n.split('.0.', 1)[-1]
    removed_short |= {s for s in short_forms(n) if '.' in s or len(s) > 3}
cmd_re = re.compile(r'^\s*#(print axioms|check|eval|reduce)\s+@?([\w.\'!?₀-₉]+)')
dropped_cmds = 0
for m in sorted(kept):
    p = DST/path_of(m)
    if protected(m): continue
    ls = p.read_text().split('\n'); out = []
    for line in ls:
        mm = cmd_re.match(line)
        if mm and mm.group(2) in removed_short:
            dropped_cmds += 1; continue
        out.append(line)
    # squeeze runs of >2 blank lines
    txt = re.sub(r'\n{4,}', '\n\n\n', '\n'.join(out))
    p.write_text(txt)
report['dropped_commands'] = dropped_cmds
report['removed_declaration_count'] = len(removed_names)
(DST/'provenance').mkdir(parents=True, exist_ok=True)
(DST/'provenance/pruning-report.json').write_text(json.dumps(report, indent=1, ensure_ascii=False))
(DST/'provenance/source-files.json').write_text(json.dumps(provenance, indent=1))
print('kept', len(kept), 'removed decls', len(removed_names), 'dropped cmds', dropped_cmds)

# 3. Docstrings describing the formerly open upper bound were rewritten by hand;
#    the edited files are stored in provenance/docstring-patches/ and copied over.
patches = DST/'provenance/docstring-patches'
if patches.exists():
    for f in patches.glob('*.lean'):
        (DST/'LRX'/f.name).write_text(f.read_text())
        print('patched', f.name)
