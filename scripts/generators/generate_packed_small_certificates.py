#!/usr/bin/env python3
"""Untrusted BFS word data; each block is checked by ordinary Lean reduction."""
import argparse
from collections import deque
from pathlib import Path
from itertools import product
from math import factorial


def codes(n):
    if n == 0:
        return [()]
    tail = codes(n-1)
    return [(i,)+tuple(0 if x+1 == i else x+1 for x in p)
            for i in range(n) for p in tail]


def witnesses(n):
    start = tuple(range(n))
    words = {start: ''}
    queue = deque([start])
    while queue:
        p = queue.popleft()
        for c,q in [('l',p[1:]+p[:1]),('r',p[-1:]+p[:-1]),('x',(p[1],p[0])+p[2:])]:
            if q not in words:
                words[q] = words[p]+c
                queue.append(q)
    return words


def pack(word):
    out=0
    for c in reversed(word):
        out=4*out+{'l':1,'r':2,'x':3}[c]
    return out


def checked_declaration(n, tail_size, code):
    statement = (f'∀ c : PermCode {tail_size},\n'
                 f'    eval (table c)=decode (n := {n}) {code} ∧ (table c).length ≤ Nat.choose {n} 2')
    if tail_size < 6:
        return 'theorem checked : ' + statement + ' := by\n  decide +kernel\n'
    import re
    from itertools import product
    depth=tail_size-4
    prefixes=list(product(*(range(tail_size-i)for i in range(depth))))
    body=statement[statement.index('    eval'):]
    out=''
    for prefix in prefixes:
        fixed='d'
        for digit,width in reversed(list(zip(prefix,range(tail_size,4,-1)))):
            fixed=f'(({digit} : Fin {width}),{fixed})'
        st=re.sub(r'\bc\b',fixed,body)
        label='_'.join(map(str,prefix))
        out+=f'private theorem checked_first_{label} : ∀ d : PermCode 4,\n'+st+' := by\n  decide +kernel\n\n'
    binders=', '.join([f'i{i}'for i in range(depth)]+['c'])
    out+='theorem checked : '+statement+' := by\n  rintro ⟨'+binders+'⟩\n  '
    out+=' <;> '.join(f'fin_cases i{i}'for i in range(depth))+'\n'
    out+=''.join('  · exact checked_first_'+'_'.join(map(str,prefix))+' c\n'for prefix in prefixes)
    return out


def generate(n, limit, tail_size):
    words=witnesses(n)
    ordered=[pack(words[p]) for p in codes(n)]
    assert max(map(len,words.values())) <= n*(n-1)//2
    directory=Path(f'LRX/PackedSmall{n}')
    directory.mkdir(exist_ok=True)
    prefixes=list(product(*(range(n-i) for i in range(n-tail_size))))
    count=len(prefixes)
    for block in range(min(count,limit or count)):
        prefix=prefixes[block]
        code='c'
        for digit,width in reversed(list(zip(prefix,range(n,n-len(prefix),-1)))):
            code=f'(⟨{digit},by decide⟩ : Fin {width}), {code}'
            code=f'({code})'
        data=ordered[block*factorial(tail_size):(block+1)*factorial(tail_size)]
        text=f'''import LRX.PackedWordCertificate

namespace LRX.PackedSmall{n}.Block{block:02d}
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def words : Array ℕ := #[{', '.join(map(str,data))}]
def table (c : PermCode {tail_size}) : List Letter := unpackWord words[codeIndex c]!

{checked_declaration(n, tail_size, code)}
#print axioms checked
end LRX.PackedSmall{n}.Block{block:02d}
'''
        (directory/f'Block{block:02d}.lean').write_text(text)
    if limit is None:
        namespace=f'PackedSmall{n}'
        imports='\n'.join(f'import LRX.{namespace}.Block{b:02d}' for b in range(count))
        cases=[]
        for b,prefix in enumerate(prefixes):
            pattern=', '.join(map(str,prefix))
            cases.append(f'  | {pattern} => Block{b:02d}.table c'+'.2'*(n-tail_size))
        parameters=', '.join('c'+'.2'*i+'.1.val' for i in range(n-tail_size))
        pattern=', '.join('_' for _ in range(n-tail_size))
        names=[f'i{i}' for i in range(n-tail_size)]
        binders=', '.join(names+['c'])
        fin_cases=' <;> '.join(f'fin_cases {name}' for name in names)
        proofs='\n'.join(f'  · simpa [table] using Block{b:02d}.checked c' for b in range(count))
        wrapper=f"""{imports}

namespace LRX.{namespace}

def table (c : PermCode {n}) : List Letter :=
  match {parameters} with
{chr(10).join(cases)}
  | {pattern} => []

theorem checked : ∀ c : PermCode {n},
    eval (table c)=decode c ∧ (table c).length ≤ Nat.choose {n} 2 := by
  intro c
  rcases c with ⟨{binders}⟩
  {fin_cases}
{proofs}

theorem sharp_words : SharpWordBound {n} := words_of_code_certificate table checked

theorem sharp_ediam : (graph {n}).ediam ≤ (Nat.choose {n} 2 : ℕ∞) :=
  sharp_ediam_of_words sharp_words

#print axioms sharp_words
#print axioms sharp_ediam
end LRX.{namespace}
"""
        Path(f'LRX/{namespace}.lean').write_text(wrapper)
    print(f'n={n}: BFS covers {len(words)} states, diameter {max(map(len,words.values()))}; emitted {min(count,limit or count)} blocks',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('sizes',type=int,nargs='+',choices=[8,9])
    parser.add_argument('--limit',type=int)
    parser.add_argument('--tail-size',type=int,choices=[5,6,7],default=6)
    args=parser.parse_args()
    for n in args.sizes:
        generate(n,args.limit,args.tail_size)
