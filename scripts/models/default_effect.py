#!/usr/bin/env python3
"""Epic's default effect, written out (#515): give `<transacts>` to every
function, method, constructor and function type of a Verse program written
without a heap specifier, so that a program written for openverse's old
rule, under which such a function was rolled back as a `<transacts>` one
is, means the same under the new one, where it has `no_rollback` and no
failure context or `<transacts>` function may call it
(docs/LANGUAGE.md, "Effect contracts").

Left as they are: `Main`; `<suspends>` functions and function types, which
no failure context calls; and functions whose code awaits or signals an
event, or spawns, which Epic's compiler refuses in a `<transacts>` function
(a spawn has `no_rollback`, #724).

  default_effect.py FILE...       annotate each file in place
  default_effect.py < IN > OUT    annotate standard input
  from default_effect import annotate
"""
import re
import sys

HEAP = ('<transacts>', '<computes>', '<reads>', '<writes>', '<allocates>', '<converges>')
DATA = ('class', 'interface', 'struct', 'enum', 'module', 'type')
KEYWORDS = ('if', 'for', 'while', 'case', 'loop', 'block', 'spawn', 'branch', 'sync', 'race', 'rush',
            'option', 'logic', 'array', 'map', 'set', 'return', 'defer', 'not', 'and', 'or', 'then',
            'else', 'where', 'var', 'do', 'first', 'Main', 'type', 'tuple', 'external', 'using')
ARG = r'(?:\[\])*(?:[A-Za-z_][A-Za-z0-9_]*(?:\([^()]*\))?)'
DEF = re.compile(
    r'(?m)(^[ \t]*|[{;][ \t]*)((?:\([^()\n]*\)\.)?(?:\([A-Za-z0-9_]+:\))?)([A-Za-z_][A-Za-z0-9_]*)'
    r'((?:<[A-Za-z_]+>)*)\(')
TYPE = re.compile(r'type\{_\(')
SIGPARAM = re.compile(r'(?<=[(,])\s*[A-Za-z_][A-Za-z0-9_]*\((?=:|\))')


def close_paren(s, i):
    depth = 0
    for k in range(i, len(s)):
        if s[k] == '(':
            depth += 1
        elif s[k] == ')':
            depth -= 1
            if depth == 0:
                return k
    return -1


def body_of(src, start, after):
    """The code of a definition: the rest of its line from `after`, and the
    lines below it indented more than the line it starts on."""
    line_start = src.rfind('\n', 0, start) + 1
    head = src[line_start:start]
    indent = len(head) - len(head.lstrip(' \t'))
    end = src.find('\n', after)
    end = len(src) if end < 0 else end
    lines = [src[after:end]]
    pos = end + 1
    while pos < len(src):
        nxt = src.find('\n', pos)
        nxt = len(src) if nxt < 0 else nxt
        line = src[pos:nxt]
        if line.strip() and len(line) - len(line.lstrip(' \t')) <= indent:
            break
        lines.append(line)
        pos = nxt + 1
    return '\n'.join(lines)


def masked(src):
    """`src` with the text of its string literals blanked (their
    interpolated code too: no definition or type is written there)."""
    out, inside = [], False
    for k, c in enumerate(src):
        if c == '"' and (k == 0 or src[k - 1] != '\\'):
            inside = not inside
            out.append(c)
        elif inside and c != '\n':
            out.append(' ')
        else:
            out.append(c)
    return ''.join(out)


def annotate(src):
    # (arrow types of simple operands, `int->int`, as function types)
    arrows = list(re.finditer(r'(' + ARG + r')->(' + ARG + r')', masked(src)))
    for m in reversed(arrows):
        src = src[:m.start()] + 'type{_(:%s):%s}' % (m.group(1), m.group(2)) + src[m.end():]
    code = masked(src)
    inserts = set()
    for m in TYPE.finditer(code):
        close = close_paren(code, m.end() - 1)
        if close < 0:
            continue
        effs = re.match(r'(?:<[A-Za-z_]+>)*', code[close + 1:]).group(0)
        if not any(h in effs for h in HEAP) and '<suspends>' not in effs:
            inserts.add(close + 1)
    for m in SIGPARAM.finditer(code):
        close = close_paren(code, m.end() - 1)
        if close < 0:
            continue
        inner = code[m.end():close]
        if inner.strip() and not inner.lstrip().startswith(':'):
            continue
        rest = re.match(r'((?:<[A-Za-z_]+>)*):', code[close + 1:])
        if rest and not any(h in rest.group(1) for h in HEAP) and '<suspends>' not in rest.group(1):
            inserts.add(close + 1)
    for m in DEF.finditer(code):
        name = m.group(3)
        if name in KEYWORDS:
            continue
        close = close_paren(code, m.end() - 1)
        if close < 0:
            continue
        params = code[m.end():close]
        if params.strip() and ':' not in params:
            continue
        rest = re.match(r'((?:<[A-Za-z_]+>)*)\s*(:=|:)\s*(\w*)', code[close + 1:])
        if not rest or (rest.group(2) == ':=' and rest.group(3) in DATA):
            continue
        # (a parametric type or alias, `pair(t:type) := …`)
        tparam = r'\s*\w+\s*:\s*(?:type|subtype\([^()]*\))\s*'
        if rest.group(2) == ':=' and re.fullmatch(tparam + r'(?:,' + tparam + r')*', params):
            continue
        effs = rest.group(1)
        if any(h in effs for h in HEAP) or '<suspends>' in effs:
            continue
        if re.search(r'\.(Await|Signal)\(|\bspawn\b', body_of(code, m.start(3), close + 1)):
            continue
        inserts.add(close + 1)
    out, pos = [], 0
    for k in sorted(inserts):
        out.append(src[pos:k])
        out.append('<transacts>')
        pos = k
    out.append(src[pos:])
    return ''.join(out)


def install():
    """Annotate every `.verse` file a test script writes through
    `pathlib.Path.write_text`, so a generator written for the old rule
    writes programs for the new one."""
    import pathlib
    write = pathlib.Path.write_text
    if getattr(write, '_default_effect', False):
        return

    def annotated(self, data, *args, **kwargs):
        if self.suffix == '.verse':
            data = annotate(data)
        return write(self, data, *args, **kwargs)
    annotated._default_effect = True
    pathlib.Path.write_text = annotated


if __name__ == '__main__':
    if len(sys.argv) > 1:
        for path in sys.argv[1:]:
            with open(path) as fh:
                text = fh.read()
            with open(path, 'w') as fh:
                fh.write(annotate(text))
    else:
        sys.stdout.write(annotate(sys.stdin.read()))
