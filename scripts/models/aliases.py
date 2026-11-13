#!/usr/bin/env python3
"""Type aliases through a generated program (Book of Verse ch. 11, "Type Aliases").

usage: aliases.py SEED < PROGRAM.verse > ALIASED.verse

An alias is the type it names (docs/research/type-aliases.md), so a program
whose types are written through aliases does what the program does: the
expectation of the model that generated it holds unchanged, but for the
positions in a refusal's message. This gives each class, interface, struct
and enum the program defines at the top level an alias, `name_alK := name` (a
parametric one, `name_alK(u0:type, ...) := name(u0, ...)`), sometimes a second
alias of that alias, all on the program's first lines (an alias may name a
class defined after it; every use is after it), and writes each use of a
type's name through one of them or not, by its own random stream: in types,
parents, constructions, casts and qualifiers alike. Text in strings and
comments is left as it is, and so is a parametric type's name with no type
arguments after it (`pair{...}`, whose arguments the expected type gives).
"""
import random
import re
import sys

DEF = re.compile(r'^([a-z_][A-Za-z0-9_]*)(\(([^()]*)\))?((?:<[a-z_]+>)*)\s*:=\s*(class|struct|interface|enum)\b')
WORD = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')


def code_spans(line):
    """The parts of a line outside strings and comments, as (start, end)."""
    spans, i, start, n = [], 0, 0, len(line)
    while i < n:
        c = line[i]
        if c == '#' or line.startswith('<#', i):
            spans.append((start, i))
            return spans
        if c == '"':
            spans.append((start, i))
            i += 1
            while i < n and line[i] != '"':
                i += 2 if line[i] == '\\' else 1
            i += 1
            start = i
            continue
        if c == "'":
            # a char literal: 'a', '\n'
            m = re.match(r"'(\\.|[^'\\])'", line[i:])
            if m:
                spans.append((start, i))
                i += len(m.group(0))
                start = i
                continue
        i += 1
    spans.append((start, n))
    return spans


def main():
    seed = int(sys.argv[1])
    rng = random.Random(seed * 1000003 + 7)
    src = sys.stdin.read()
    lines = src.split('\n')
    words = set(WORD.findall(src))
    types = {}  # name -> number of type parameters
    for ln in lines:
        m = DEF.match(ln)
        if m:
            params = [p for p in (m.group(3) or '').split(',') if p.strip()]
            types[m.group(1)] = len(params)
    if not types:
        sys.stdout.write(src)
        return
    defs, names = [], {}
    for t, k in types.items():
        chain = []
        for _ in range(rng.choice([1, 1, 2])):
            j = 0
            while f'{t}_al{j}' in words or any(f'{t}_al{j}' == a for a in chain):
                j += 1
            chain.append(f'{t}_al{j}')
        prev = t
        for a in chain:
            if k == 0:
                defs.append(f'{a} := {prev}')
            else:
                ps = [f'u{i}' for i in range(k)]
                while any(p in words for p in ps):
                    ps = [p + '_' for p in ps]
                defs.append(f'{a}({", ".join(p + ":type" for p in ps)}) := {prev}({", ".join(ps)})')
            prev = a
        names[t] = chain
    out = []
    for ln in lines:
        m = DEF.match(ln)
        head = len(m.group(1)) if m else 0
        pieces, last = [], 0
        for (a, b) in code_spans(ln):
            for w in WORD.finditer(ln, a, b):
                t = w.group(0)
                if t not in names or w.start() < head:
                    continue
                before = ln[:w.start()].rstrip()
                after = ln[w.end():]
                # (a member, `X.name`, or a named argument or field, `name :=`)
                if before.endswith('.') or re.match(r'\s*:=', after) or re.match(r'\s*:[^=)]', after):
                    continue
                if types[t] > 0 and not after.startswith('('):
                    continue
                if rng.random() < 0.5:
                    continue
                pieces.append(ln[last:w.start()])
                pieces.append(rng.choice(names[t]))
                last = w.end()
        pieces.append(ln[last:])
        out.append(''.join(pieces))
    # the aliases first, after a first line that is a comment
    at = 1 if out and out[0].lstrip().startswith('#') else 0
    sys.stdout.write('\n'.join(out[:at] + defs + out[at:]))


if __name__ == '__main__':
    main()
