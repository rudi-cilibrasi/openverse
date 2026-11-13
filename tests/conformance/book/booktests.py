#!/usr/bin/env python3
"""Measure openverse against the Book of Verse's own tests.

The Book of Verse repository (https://github.com/verselang/book) carries a copy
of the Verse compiler's development tests, `Tests/**/*.versetest`. This script
reads a checkout of it at the pinned revision (docs/research/book-test-conformance.md
gives the revision and how each test form is read), turns every test case into a
program openverse can check or run, runs it with the Lean front end and
interpreter (and the C runtime where the program runs), and records a verdict
for each case. It never copies the Book's tests into this repository: the
programs it writes live in a work directory outside it, and the baseline holds
identifiers and verdicts only.

  booktests.py run BOOK [--work DIR] [--jobs N] [--only SUBSTR] [--results FILE] [--causes]
      run every case and print the totals per file; --results writes one line
      per case (id, form, expectation, tags, verdict, cause, detail), and
      --causes also prints the counts by cause (causes.py)
  booktests.py compare BOOK [--baseline FILE] [run options]
      run, then report the cases whose verdict changed against the baseline
      (worse or better); exits 1 when a case got worse
  booktests.py baseline BOOK [--baseline FILE] [run options]
      run and write the baseline
  booktests.py show BOOK CASE [--work DIR]
      print the program a case translates to

BOOK is the root of the checkout (the directory that holds Tests/).
"""

import argparse
import concurrent.futures
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field

sys.dont_write_bytecode = True   # no __pycache__ in the repository
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import causes  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
OPENVERSE = os.path.join(ROOT, ".lake", "build", "bin", "openverse")
CVERSE = os.path.join(ROOT, "runtime", "build", "cverse")
PARSE_ONLY = os.path.join(os.path.dirname(os.path.abspath(__file__)), "ParseOnly.lean")
BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "baseline.tsv")
PINNED = "beaa719ba165cbf33eff462f2b0fe078a6dd9ab0"

# Seconds a single openverse or cverse process may take, and the fuel both get
# (a tenth of openverse's default: a Book test that loops forever then ends in
# a few seconds, well inside the timeout, so verdicts do not depend on load).
TIMEOUT = 60
FUEL = "10000000"
MEM_BYTES = 4 * 1024 ** 3

# ---------------------------------------------------------------------------
# Lexical masking: the same text with comments blanked and string contents
# blanked (except the code of their {interpolations}), so that brackets,
# identifiers and keywords can be found by position.
# ---------------------------------------------------------------------------


def mask(text):
    out = list(text)
    n = len(text)
    # the stack of lexical modes: ["code", 0], ["str", 0] or ["interp", brace depth]
    stack = [["code", 0]]
    i = 0

    def blank(a, b):
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    def line_start(k):
        return text.rfind("\n", 0, k) + 1

    while i < n:
        mode = stack[-1][0]
        c = text[i]
        if mode == "str":
            if c == "\\":
                blank(i, i + 2)
                i += 2
            elif c == '"':
                stack.pop()
                i += 1
            elif c == "{":
                out[i] = " "
                stack.append(["interp", 0])
                i += 1
            elif c == "\n":  # an unterminated string ends with its line
                stack.pop()
                i += 1
            else:
                out[i] = " "
                i += 1
            continue
        # code or interpolation
        if text.startswith("<#>", i):
            ls = line_start(i)
            indent = len(text[ls:i]) - len(text[ls:i].lstrip(" \t"))
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            # every following line indented more than the <#> line (or blank)
            while j < n:
                k = text.find("\n", j + 1)
                k = n if k < 0 else k
                line = text[j + 1:k]
                if line.strip() == "" or (len(line) - len(line.lstrip(" \t"))) > indent:
                    blank(j + 1, k)
                    j = k
                else:
                    break
            i = j
            continue
        if text.startswith("<#", i):
            depth = 0
            j = i
            while j < n:
                if text.startswith("<#", j):
                    depth += 1
                    j += 2
                elif text.startswith("#>", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            blank(i, j)
            i = j
            continue
        if c == "#":
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
            continue
        if c == '"':
            stack.append(["str", 0])
            i += 1
            continue
        if c == "'":
            j = i + 1
            if j < n and text[j] == "\\":
                j += 2
            else:
                j += 1
            if j < n and text[j] == "'":
                blank(i + 1, j)
                i = j + 1
                continue
            i += 1
            continue
        if mode == "interp":
            if c == "{":
                stack[-1][1] += 1
            elif c == "}":
                if stack[-1][1] == 0:
                    out[i] = " "
                    stack.pop()
                    i += 1
                    continue
                stack[-1][1] -= 1
        i += 1
    return "".join(out)


OPEN = "([{"
CLOSE = ")]}"


def match_bracket(m, i):
    """Index of the bracket closing the one at m[i], in masked text m."""
    depth = 0
    for j in range(i, len(m)):
        if m[j] in OPEN:
            depth += 1
        elif m[j] in CLOSE:
            depth -= 1
            if depth == 0:
                return j
    return -1


def dedent(lines):
    ind = [len(l) - len(l.lstrip(" \t")) for l in lines if l.strip()]
    k = min(ind) if ind else 0
    return [l[k:] if l.strip() else "" for l in lines]


# ---------------------------------------------------------------------------
# Segmentation of a .versetest file into its top-level items.
# ---------------------------------------------------------------------------

WRAPPERS = {"bp_vm_only": "bp", "verse_vm_only": "verse", "verse_vm_todo": "verse_vm_todo",
            "auto_qualify_todo": "auto_qualify_todo"}
CONTINUATIONS = ("else", "then", "until", "catch")


@dataclass
class Item:
    line: int          # 1-based line in the .versetest file
    text: str          # original text of the item
    mtext: str         # its masked text
    comment: list      # the comment lines just before it
    tags: tuple = ()   # enclosing wrappers


def segment(text, mtext, line0, tags):
    """Split a body of top-level items. line0 is the file line of text's first line."""
    lines = text.split("\n")
    mlines = mtext.split("\n")
    items = []          # [first line index, lines, masked lines, leading comment]
    depth = 0
    tail = []           # blank or comment-only lines after the current item
    pending = []        # the comment lines just before the next item
    col = 0             # the indentation of the current item's first line
    for idx, (l, ml) in enumerate(zip(lines, mlines)):
        ind = len(ml) - len(ml.lstrip(" \t"))
        code = ml.strip()
        # An item starts at depth 0 on a line indented no more than the item
        # before it (inside braces, items need not start at column 0).
        starts = (depth == 0 and code != "" and (not items or ind <= col)
                  and code[0] not in "{[" + CLOSE
                  and not re.match(r"(%s)\b" % "|".join(CONTINUATIONS), code))
        if starts:
            items.append([idx, [l], [ml], [c.strip() for c in pending]])
            tail, pending, col = [], [], ind
        elif items and (ml.strip() != "" or depth > 0):
            # a continuation: the blank and comment lines before it are the item's
            items[-1][1].extend(t for t, _ in tail)
            items[-1][2].extend(mt for _, mt in tail)
            items[-1][1].append(l)
            items[-1][2].append(ml)
            tail, pending = [], []
        else:
            tail.append((l, ml))
            pending = pending + [l] if l.strip() else []
            continue
        for ch in ml:
            depth = max(0, depth + (ch in OPEN) - (ch in CLOSE))
    out = []
    for idx, ls, mls, com in items:
        k = len(mls[0]) - len(mls[0].lstrip(" \t"))
        if k:   # an item indented inside braces: as if it started at column 0
            ls = [x[k:] if x[:k].strip() == "" else x.lstrip() for x in ls]
            mls = [x[k:] if x[:k].strip() == "" else x.lstrip() for x in mls]
        out.append(Item(line0 + idx, "\n".join(ls), "\n".join(mls), com, tags))
    return out


@dataclass
class Form:
    """An item read as head(args) body."""
    head: str
    args: str          # original text inside the parentheses, or None
    body: str          # original text of the body (dedented), or None
    mbody: str
    body_line: int     # file line of the body's first line
    braced: bool
    specs: tuple = ()  # specifiers on the head: <depends_on_library>


def read_form(item):
    """Read an item as `head`, optional `(args)`, then `{body}` or `: body`."""
    t, m = item.text, item.mtext
    mo = re.match(r"\s*([A-Za-z_][A-Za-z0-9_]*)", m)
    if not mo:
        return None
    head = mo.group(1)
    i = mo.end()
    # specifiers after the head: assert_valid<depends_on_library>{...}
    spec = re.match(r"(\s*<\s*[A-Za-z_]\w*\s*>)+", m[i:])
    specs = ()
    if spec and head.startswith("assert"):
        specs = tuple(re.findall(r"[A-Za-z_]\w*", spec.group(0)))
        i += spec.end()
    args = None
    j = i
    while j < len(m) and m[j] in " \t":
        j += 1
    if j < len(m) and m[j] == "(":
        k = match_bracket(m, j)
        if k < 0:
            return None
        args = t[j + 1:k]
        i = k + 1
    j = i
    while j < len(m) and m[j] in " \t\r\n":
        j += 1
    if j >= len(m):
        return Form(head, args, None, None, item.line, False, specs)
    if m[j] == "{":
        k = match_bracket(m, j)
        if k < 0:
            return None
        body, mbody = t[j + 1:k], m[j + 1:k]
        line = item.line + t.count("\n", 0, j + 1)
        bl, mbl = body.split("\n"), mbody.split("\n")
        if len(bl) > 1:
            first, mfirst = bl[0], mbl[0]
            rest, mrest = bl[1:], mbl[1:]
            if mfirst.strip() == "":
                first = None
                line += 1
            k2 = [len(x) - len(x.lstrip(" \t")) for x, y in zip(rest, mrest) if y.strip()]
            ind = min(k2) if k2 else 0
            rest = [x[ind:] if y.strip() else "" for x, y in zip(rest, mrest)]
            mrest = [y[ind:] if y.strip() else "" for y in mrest]
            # drop the blank last line before the closing brace
            while rest and rest[-1].strip() == "":
                rest.pop()
                mrest.pop()
            if first is not None:
                rest = [first.strip()] + rest
                mrest = [mfirst.strip()] + mrest
            body, mbody = "\n".join(rest), "\n".join(mrest)
        else:
            body, mbody = body.strip(), mbody.strip()
        return Form(head, args, body, mbody, line, True, specs)
    if m[j] == ":" or (m[j] == "." and m[j + 1:j + 2] in (" ", "\t")):
        # `head: body` (indented, or on the same line) or `head. expression`
        nl = t.find("\n", j)
        nl = len(t) if nl < 0 else nl
        same = t[j + 1:nl]
        msame = m[j + 1:nl]
        rest = t[nl + 1:].split("\n") if nl < len(t) else []
        mrest = m[nl + 1:].split("\n") if nl < len(m) else []
        line = item.line + t.count("\n", 0, j) + 1
        k2 = [len(x) - len(x.lstrip(" \t")) for x, y in zip(rest, mrest) if y.strip()]
        ind = min(k2) if k2 else 0
        rest = [x[ind:] if y.strip() else "" for x, y in zip(rest, mrest)]
        mrest = [y[ind:] if y.strip() else "" for y in mrest]
        while rest and mrest[-1].strip() == "":
            rest.pop()
            mrest.pop()
        if msame.strip():
            rest = [same.strip()] + rest
            mrest = [msame.strip()] + mrest
            line -= 1
        return Form(head, args, "\n".join(rest), "\n".join(mrest), line, False, specs)
    return Form(head, args, None, None, item.line, False, specs)


def flatten(text, mtext, line0, tags=()):
    """The items of a file, with the contents of VM wrappers spliced in, tagged."""
    out = []
    for it in segment(text, mtext, line0, tags):
        f = read_form(it)
        if f and f.head in WRAPPERS and f.args is None and f.body is not None:
            sub = flatten(f.body, f.mbody, f.body_line, tags + (WRAPPERS[f.head],))
            if sub and it.comment:
                sub[0].comment = it.comment + sub[0].comment
            out.extend(sub)
        else:
            out.append(it)
    return out


# ---------------------------------------------------------------------------
# Test cases.
# ---------------------------------------------------------------------------

# What each assertion form expects, and the phase an expected error belongs to.
RUNTIME_FORMS = {"assert": "succeeds", "assert_runtime_error": "runtime-error",
                 "assert_success_or_runtime_error": "runs"}
SNIPPET_FORMS = {"assert_valid": ("valid", ""), "assert_link_valid": ("valid", ""),
                 "assert_semantic_error": ("error", "semantic"),
                 "assert_link_error": ("error", "link"), "assert_ir_error": ("error", "ir"),
                 "assert_syntax_error": ("error", "syntax")}
SYNTAX_FORMS = {"assert_valid_syntax", "assert_roundtrip"}
# Forms that check compiler output openverse has no counterpart for.
TOOLING_FORMS = {"assert_bytecode", "assert_digest_generated", "assert_auto_qualification",
                 "assert_persistence_snapshot", "assert_fingerprint_determinism",
                 "assert_used_assets", "assert_exported_metadata", "incremental_compilation"}
HARNESS_ITEMS = {"vmodule", "vpackage"}

# The test script module /Verse.org/Tests/VerseTestScriptCmd and its submodules
# (CoroUtils, TestUtils, ...) belong to the compiler's test runner: the Book does
# not define them. A case that uses one of their members is not translatable.
# The unqualified names are those the tests use after `using` the submodule;
# they count only where the program does not define them itself.
TEST_MODULES = ["CoroUtils", "TestUtils", "ProfUtils", "FunctionUtils", "FloatConstants",
                "ModuleDefsUtils"]
TEST_NAMES = {
    "FloatConstants": ["DoubleMax", "PosInfty", "SmallestNormal", "HalfSmallestNormal",
                       "LargestSubnormal", "SmallestSubnormal", "SmallestNormalTimesOneHalf",
                       "JustUnderHalfSmallestNormal", "Pow2_52", "Pow2_64", "Pow2_Minus25",
                       "Pow2_Minus28"],
    "CoroUtils": ["LogEvent", "GetEventLogString", "WaitTicks", "Tick", "GetNumActiveCoroutines",
                  "SuppressNextReset", "ResetThenLogEvent", "SignalTransacts"],
    "TestUtils": ["InvokeTransacts", "AreClassesEqual", "BitcastFloatToInt"],
    # Definitions the tests use that neither their file, the Book's chapters
    # nor its Runtime API reference define: natives and classes of the compiler's
    # test runner. Found as openverse's "unknown ..." refusals whose name no
    # line of the file defines and the API reference does not mention, each
    # then checked by hand (book-test-conformance.md, "Not translatable").
    "the test runner": [
        "serializable_class", "SerializeAndDeserialize", "native_deeply_mutable",
        "TestGenerators", "TestForEachSubobject", "TestNamedParams", "test_vni",
        "TestAvailableAttribute", "unique_interface", "unique_class", "test_parametric_class",
        "SOL8380_interface", "SOL8380_class_only_accessors", "test_native_parametric_type",
        "test_native_parametric_iface", "test_native_parametric_impl", "callable_class",
        "callable_subclass", "ParamAlignment", "duplication_test_inner_base", "test_interface",
        "TestNestedNamedTupleParameters", "test_external_parametric_type",
        "test_external_parametric_type2", "test_external_parametric_type3",
        "test_external_parametric_type6", "reference_test_base", "int_to_int_function",
        "struct_to_int_function", "class_a_interface_a", "accessors_test_runtime_error",
        "UE234933_interface", "UE234933_interface_var", "MakeObjectWithNullField",
        "MakeObjectWithNullOptional", "MakeObjectWithNullArrayElement", "MakeObjectWithEmptyArray",
        "MakeObjectWithNullTupleElement", "MakeObjectWithNullMapKey", "MakeObjectWithNullMapValue",
        "TestNativeTypeFunction", "TestPrintScriptCallstack", "TestRuntimeWarningCallstack",
        "TestRuntimeErrorHasValidCallstack", "TestComputationLimitHasValidCallstack",
        "MultiResultTupleNested", "no_defun_easy", "ToInteger",
        "MakeExternalConstructorFunctionClass1", "external_constructor_function_class1",
        "c_test", "e_test", "f_test", "g_test", "test_object_to_json_base",
        "TestParametricFunction", "TestNestedUniversalQuantifier", "UseRational", "class_a",
        "test_struct", "test_class_alias", "test_struct_alias", "test_var",
        "native_persistable_class1", "native_persistable_struct1", "native_persistable_enum1",
        "native_persistable_struct2", "external_persistable_class1",
        "external_persistable_struct1", "external_persistable_enum1",
        # extension methods of the test runner ("The method is defined in
        # /Verse.org/Tests/VerseTestScriptCmd", ExtensionFields.versetest:157)
        "TakeExtension", "PlusTwo", "TestParametricExtensionMethod"],
}
# Engine APIs the Book's Runtime API reference places outside the language:
# persistence, JSON, Unreal objects and AutoRTFM. A case using one is not
# translatable.
ENGINE_NAMES = ["Persistence", "persistent_key", "FromJson", "ToJson", "IsUObject",
                "GetUObjectPathName", "IsAutoRTFMEnabled"]


# Stand-ins for test runner definitions whose behaviour cannot change a verdict.
# DebugPrint only prints a diagnostic (the tests call it from <computes>
# functions, on their failure paths); the stand-in prints nothing.
STANDINS = {"DebugPrint": "DebugPrint(Message:any)<computes>:void = {}"}


def with_standins(prog):
    """A program with the stand-ins it uses and does not define, at its end."""
    m = mask(prog)
    ids = idents("\n".join(l for l in m.split("\n") if not re.match(r"\s*using\b", l)))
    add = [STANDINS[n] for n in sorted(STANDINS) if n in ids and n not in program_defs(m)]
    return "\n".join([prog] + add) if add else prog


@dataclass
class Case:
    id: str
    file: str
    line: int
    form: str
    expect: str        # succeeds | runtime-error | runs | valid | error | parses | ""
    phase: str = ""    # for expected errors: syntax | semantic | link | ir
    tags: tuple = ()
    codes: str = ""
    programs: list = field(default_factory=list)  # [(wrapping, text)]
    nt: str = ""       # why the case is not translatable
    comment: list = field(default_factory=list)
    cause: str = ""    # for a disagreement: its cause (causes.py)


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def idents(mtext):
    return set(IDENT.findall(mtext))


def decl_names(mtext):
    """The names a top-level definition defines (from its masked text)."""
    first = mtext.lstrip()
    m = re.match(r"\((?:[A-Za-z_]\w*)?\s*:[^()]*(?:\([^()]*\))*[^()]*\)\s*\.\s*([A-Za-z_]\w*)", first)
    if m:   # extension method (X:t).Name
        return {m.group(1)}
    m = re.match(r"\([^()]*:\)\s*([A-Za-z_]\w*)", first)
    if m:   # qualified name (q:)Name
        return {m.group(1)}
    m = re.match(r"(?:var\s+)?(?:<[^>]*>\s*)*([A-Za-z_]\w*)", first)
    return {m.group(1)} if m else set()


def module_names(text, mtext):
    """The names a definition defines, with every member of a module definition
    (which a `using` of the module makes visible)."""
    names = decl_names(mtext)
    first = mtext.split("\n")[0]
    if re.search(r":=\s*module\s*[:{]?\s*$", first) or re.search(r":=\s*module\s*\{", first):
        f = read_form(Item(1, re.sub(r"^.*?:=\s*", "", text, count=1),
                           re.sub(r"^.*?:=\s*", "", mtext, count=1), []))
        if f and f.body is not None:
            for sub in segment(f.body, f.mbody, 1, ()):
                names |= module_names(sub.text, sub.mtext)
    return names


def unescape(s):
    out, i = [], 0
    while i < len(s):
        if s[i] == "\\" and i + 1 < len(s):
            c = s[i + 1]
            out.append({"n": "\n", "t": "\t", "r": "\r"}.get(c, c))
            i += 2
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def string_body(body, mbody):
    """The source text of a body that is a single string literal, else None."""
    if body and re.fullmatch(r'\s*"\s*"\s*', mbody) and body.strip().startswith('"'):
        return unescape(body.strip()[1:-1])
    return None


def split_top(text):
    """A snippet with its `;`-separated top-level definitions on lines of their own."""
    m = mask(text)
    out = []
    depth = 0
    for l, ml in zip(text.split("\n"), m.split("\n")):
        if depth == 0 and l[:1] not in (" ", "\t", "") and ";" in ml:
            start, d = 0, 0
            for k, ch in enumerate(ml):
                d += (ch in OPEN) - (ch in CLOSE)
                if ch == ";" and d == 0:
                    if l[start:k].strip():
                        out.append(l[start:k].strip())
                    start = k + 1
            if l[start:].strip():
                out.append(l[start:].strip())
        else:
            out.append(l)
        for ch in ml:
            depth = max(0, depth + (ch in OPEN) - (ch in CLOSE))
    return "\n".join(out)


def indent(text, n=4):
    return "\n".join((" " * n + l) if l.strip() else "" for l in text.split("\n"))


def defines_main(mtext):
    return re.search(r"(?m)^Main\s*(<[^>]*>\s*)*\(", mtext) is not None


STUB_MAIN = "Main():void = {}"


@dataclass
class Decl:
    names: set
    text: str
    mtext: str
    tags: tuple
    uses: set
    harness: bool = False   # a vmodule/vpackage item


def vm_of(tags):
    for t in tags:
        if t in ("bp", "verse"):
            return t
        if t == "verse_vm_todo":
            return "bp"     # runs on the BPVM only: a known VerseVM failure
    return None


def visible(decls, tags):
    vm = vm_of(tags)
    return [d for d in decls if vm_of(d.tags) in (None, vm)]


OPERATORS = {"operator", "prefix", "postfix"}


def closure(decls, mtext):
    """The definitions a text needs, transitively, by the names it mentions."""
    need = idents(mtext)
    defined = set().union(*[d.names for d in decls]) if decls else set()
    taken = [False] * len(decls)
    changed = True
    while changed:
        changed = False
        for k, d in enumerate(decls):
            if taken[k]:
                continue
            hit = d.names & need
            if d.names & OPERATORS:
                # an operator definition (operator'+', prefix'-') is used through
                # its symbol: it is needed with a definition its signature names,
                # or, when that names only built-in types, where the symbol occurs
                sym = re.match(r"\s*(?:operator|prefix|postfix)'([^']+)'", d.text)
                local = d.uses & defined - OPERATORS
                hit = (any(taken[j] and decls[j].names & d.uses for j in range(len(decls)))
                       if local else bool(sym and sym.group(1) in mtext))
            if hit:
                taken[k] = True
                need |= d.uses
                changed = True
    return [d for k, d in enumerate(decls) if taken[k]]


def program_defs(mtext):
    """The names the top-level items of a (masked) program define."""
    names = set()
    for it in segment(mtext, mtext, 1, ()):
        names |= decl_names(it.mtext)
    return names


def static_nt(mtext):
    """Why a program cannot be translated, from the identifiers it uses
    (outside its `using` lines)."""
    code = "\n".join(l for l in mtext.split("\n") if not re.match(r"\s*using\b", l))
    ids = idents(code)
    for api in TEST_MODULES:
        if api in ids:
            return "test API: %s" % api
    loose = {n: mod for mod, ns in TEST_NAMES.items() for n in ns}
    hit = sorted(n for n in ids & set(loose) if n not in program_defs(code))
    if hit:
        return "test API: %s (%s)" % (loose[hit[0]], hit[0]) if loose[hit[0]] != \
            "the test runner" else "test API: the test runner's %s" % hit[0]
    hit = sorted(n for n in ids & set(ENGINE_NAMES) if n not in program_defs(code))
    if hit:
        return "engine API: %s" % hit[0]
    if "native" in ids and re.search(r"<\s*native\s*>", code):
        return "engine: <native> definitions"
    if ids & {"vpackage", "vmodule"}:
        return "harness: vpackage/vmodule"
    if ids & {"bp_vm_only", "verse_vm_only"}:
        return "harness: VM-conditional code inside a case"
    return ""


def build_cases(book, rel):
    path = os.path.join(book, rel)
    with open(path, encoding="utf-8") as fh:
        text = fh.read().replace("\r\n", "\n").replace("\r", "\n")
    if text.startswith("﻿"):
        text = text[1:]
    items = flatten(text, mask(text), 1)
    decls, usings, asserts = [], [], []
    for it in items:
        f = read_form(it)
        head = f.head if f else ""
        if head == "using":
            usings.append(it)
        elif head.startswith("assert") or head in TOOLING_FORMS:
            asserts.append((it, f))
        elif head in HARNESS_ITEMS:
            names = idents(it.mtext)
            decls.append(Decl(names, it.text, it.mtext, it.tags, set(), harness=True))
        else:
            decls.append(Decl(module_names(it.text, it.mtext), it.text, it.mtext, it.tags,
                              idents(it.mtext)))
    cases = []
    seen = {}

    def new_case(line, form, expect, it, f=None, phase=""):
        cid = "%s:%d" % (rel, line)
        seen[cid] = seen.get(cid, 0) + 1
        if seen[cid] > 1:
            cid += "#%d" % seen[cid]
        c = Case(cid, rel, line, form, expect, phase,
                 (it.tags if it else ()) + (f.specs if f else ()),
                 (f.args or "").strip() if f else "", comment=it.comment if it else [])
        cases.append(c)
        return c

    def prelude_for(mtext, tags):
        """Usings and the needed shared definitions, or a reason they cannot be had."""
        need = closure(visible(decls, tags), mtext)
        if any(d.harness for d in need):
            return None, "harness: vpackage/vmodule"
        names = set().union(*[d.names for d in need]) if need else set()
        uses = []
        for u in usings:
            if vm_of(u.tags) not in (None, vm_of(tags)):
                continue
            target = idents(u.mtext) - {"using"}
            if "/" in u.mtext or target & names:
                uses.append(u.text)
            elif any(d.harness and d.names & target for d in decls):
                return None, "harness: vpackage/vmodule"
        return [split_top(t) for t in uses + [d.text for d in need]], ""

    for it, f in asserts:
        form = f.head
        if form in TOOLING_FORMS:
            c = new_case(it.line, form, "", it, f)
            c.nt = "tooling: %s" % form
            continue
        if f.body is None:
            c = new_case(it.line, form, "", it, f)
            c.nt = "harness: no body"
            continue
        if form in RUNTIME_FORMS:
            c = new_case(it.line, form, RUNTIME_FORMS[form], it, f)
            body = f.body
            if f.braced and "\n" not in body:
                main = "Main()<decides>:void = {%s}" % body
            elif f.braced:
                main = "Main()<decides>:void = {\n%s\n}" % indent(body)
            else:
                main = "Main()<decides>:void =\n%s" % indent(body)
            pre, why = prelude_for(f.mbody, it.tags)
            if why:
                c.nt = why
                continue
            if any(defines_main(mask(p)) for p in pre):
                c.nt = "harness: the file defines Main"
                continue
            c.programs = [("main", with_standins("\n".join(pre + [main])) + "\n")]
        elif form in SNIPPET_FORMS or form in SYNTAX_FORMS:
            if form in SNIPPET_FORMS:
                expect, phase = SNIPPET_FORMS[form]
            else:
                expect, phase = "parses", ""
            c = new_case(it.line, form, expect, it, f, phase)
            src = f.body
            if form == "assert_roundtrip" and f.args is not None:
                src = f.args      # assert_roundtrip(SOURCE){PRINTED}: parse SOURCE
            elif string_body(f.body, f.mbody) is not None:
                src = string_body(f.body, f.mbody)
            elif f.braced and "\n" not in src:
                src = src.strip()
            src = "\n".join(dedent(src.split("\n")))
            body = "BookSyntax():void =\n%s\n" % indent(src)
            if form in SYNTAX_FORMS:
                # parsed only, exactly as written, and as the body of a function
                c.programs = [("top", src + "\n"), ("body", body)]
            elif form == "assert_syntax_error":
                # parsed exactly as written; when that parses, compiled with a Main
                full = src if defines_main(mask(src)) else src + "\n\n" + STUB_MAIN
                c.programs = [("full", full + "\n"), ("top", src + "\n"), ("body", body)]
            else:
                # definitions: `;`-separated ones on lines of their own, and a Main
                top = split_top(src)
                prog = top if defines_main(mask(top)) else top + "\n\n" + STUB_MAIN
                c.programs = [("top", with_standins(prog) + "\n")]
        else:
            c = new_case(it.line, form, "", it, f)
            c.nt = "harness: unknown form %s" % form
            continue
        why = static_nt(mask(c.programs[0][1])) if c.programs else ""
        if why:
            c.nt = why
    plain = [d for d in decls if vm_of(d.tags) is None]
    if not asserts and (decls or usings):
        # A file of definitions only: the whole file is expected to compile.
        c = new_case(1, "file", "valid", None)
        prog = "\n".join(split_top(x.text) for x in usings + decls)
        if not defines_main(mask(prog)):
            prog += "\n\n" + STUB_MAIN
        c.programs = [("top", with_standins(prog) + "\n")]
        if any(d.harness for d in decls):
            c.nt = "harness: vpackage/vmodule"
        else:
            c.nt = static_nt(mask(prog))
    elif asserts and plain:
        # The definitions every runtime assertion of the file is compiled with.
        c = new_case(0, "decls", "valid", None)
        c.id = "%s:decls" % rel
        if any(d.harness for d in plain):
            c.nt = "harness: vpackage/vmodule"
        prog = "\n".join(split_top(x.text) for x in [u for u in usings if vm_of(u.tags) is None] + plain)
        if not defines_main(mask(prog)):
            prog += "\n\n" + STUB_MAIN
        c.programs = [("top", with_standins(prog) + "\n")]
        c.nt = c.nt or static_nt(mask(prog))
    return cases


def all_cases(book, only=None):
    tests = os.path.join(book, "Tests")
    rels = []
    for d, _, fs in os.walk(tests):
        for f in fs:
            if f.endswith(".versetest"):
                rels.append(os.path.relpath(os.path.join(d, f), book).replace(os.sep, "/"))
    rels.sort()
    if only:
        rels = [r for r in rels if only in r]
    cases = []
    for r in rels:
        cases.extend(build_cases(book, r))
    return cases


# ---------------------------------------------------------------------------
# Running openverse.
# ---------------------------------------------------------------------------


def limit_memory():
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (MEM_BYTES, MEM_BYTES))


def run(cmd, timeout=TIMEOUT):
    """(exit code, stdout, stderr); exit None when it timed out."""
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=timeout, preexec_fn=limit_memory)
        return p.returncode, p.stdout.decode("utf-8", "replace"), p.stderr.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        return None, "", "timeout after %ds" % timeout


def case_dir(work, cid):
    return os.path.join(work, "progs", re.sub(r"[^A-Za-z0-9_.#/-]", "_", cid.replace(":", "/")))


def write_programs(work, cases):
    for c in cases:
        d = case_dir(work, c.id)
        os.makedirs(d, exist_ok=True)
        for wrap, text in c.programs:
            path = os.path.join(d, wrap + ".verse")
            old = None
            if os.path.exists(path):
                with open(path, encoding="utf-8") as fh:
                    old = fh.read()
            if old != text:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)


def parse_only(work, paths, jobs):
    """{path: (ok, message)} from the parse-only driver, in parallel batches."""
    out = {}
    if not paths:
        return out
    paths = sorted(paths)
    size = max(1, (len(paths) + jobs - 1) // jobs)
    batches = [paths[k:k + size] for k in range(0, len(paths), size)]

    def one(k):
        lst = os.path.join(work, "parse-%d.list" % k)
        with open(lst, "w", encoding="utf-8") as fh:
            fh.write("\n".join(batches[k]) + "\n")
        p = subprocess.run(["lake", "env", "lean", "--run", PARSE_ONLY, lst], cwd=ROOT,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        res = {}
        for line in p.stdout.decode("utf-8", "replace").split("\n"):
            parts = line.split("\t")
            if len(parts) >= 2:
                res[parts[0]] = (parts[1] == "ok", parts[2] if len(parts) > 2 else "")
        if p.returncode != 0 or len(res) != len(batches[k]):
            sys.exit("ParseOnly.lean failed on %s:\n%s" % (lst, p.stderr.decode()[-2000:]))
        return res

    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for res in ex.map(one, range(len(batches))):
            out.update(res)
    return out


INVARIANT_ERRORS = ("error: type", "error: slot", "error: call", "error: control")


def first_line(s):
    for l in s.split("\n"):
        if l.strip():
            return l.strip()
    return ""


def diag(err, path):
    """openverse's diagnostic without the file name."""
    d = first_line(err)
    if d.startswith(path + ":"):
        d = d[len(path) + 1:]
    return d


def run_program(path):
    """Compile and run a program with the Lean interpreter and, when it compiles,
    with the C runtime. Returns a dict describing the outcome."""
    vbc = path[:-len(".verse")] + ".vbc"
    if os.path.exists(vbc):
        os.remove(vbc)
    rc, out, err = run([OPENVERSE, "run", path, "--fuel", FUEL, "--emit", vbc])
    # (the Lean runtime out of memory: its allocator prints this and exits with
    # 1, which no Lean program can catch; it is the resource limit cverse
    # reports as `limit: memory`, exit 3: docs/FORMAT.md, "Exit protocol")
    if rc == 1 and first_line(err) == "INTERNAL PANIC: out of memory":
        rc, err = 3, "limit: memory\n"
    r = {"rc": rc, "out": out, "err": err, "diag": diag(err, path)}
    if rc is None:
        r["internal"] = "hang (Lean): no result in %ds" % TIMEOUT
        return r
    if rc not in (0, 1, 2, 3, 4):
        r["internal"] = "crash (Lean): exit %d: %s" % (rc, first_line(err)[:200])
        return r
    if "internal error" in err or "PANIC" in err:
        r["internal"] = "Lean: %s" % r["diag"][:300]
        return r
    if rc == 4:
        return r
    if not os.path.exists(vbc):
        r["internal"] = "Lean ran the program but wrote no bytecode"
        return r
    crc, cout, cerr = run([CVERSE, vbc, "--fuel", FUEL])
    if crc is None:
        r["internal"] = "hang (C): no result in %ds; Lean exit %d" % (TIMEOUT, rc)
    elif (crc, cout, cerr) != (rc, out, err):
        r["internal"] = "Lean/C disagree: Lean exit %d %r, C exit %s %r" % (
            rc, (out + err)[-120:], crc, (cout + cerr)[-120:])
    elif rc == 2 and first_line(err).startswith(INVARIANT_ERRORS):
        r["internal"] = "accepted program raised %s" % first_line(err)
    return r


# A refusal at elaboration whose diagnostic says openverse lacks a feature or a
# name, rather than that a rule of the language is broken: an expected error
# refused this way agrees, but not for the reason the test checks.
UNSUPPORTED = re.compile(r"unknown |not supported|unsupported|only structs can be parametric"
                         r"|openverse supports|is a module, not a value|is not a value"
                         r"|not yet|cannot be (?:used )?as a value")


def refusal_kind(phase, diagnostic):
    if phase == "parse":
        return "parse"
    return "unsupported" if UNSUPPORTED.search(diagnostic) else "rule"


VERDICTS = ["agrees", "disagrees-accepts", "disagrees-refuses", "wrong-output",
            "not-translatable", "internal-error"]


def verdict(c, results, parsed, work):
    """(verdict, detail) of a case."""
    if c.nt:
        return "not-translatable", c.nt
    d = case_dir(work, c.id)
    if c.expect == "parses":
        tried = []
        for wrap, _ in c.programs:
            ok, msg = parsed[os.path.join(d, wrap + ".verse")]
            if ok:
                return "agrees", "parses (%s)" % wrap
            # how far into the snippet the parser got (the body wrapping adds a
            # line before it and four columns)
            m = re.match(r"(\d+):(\d+):", msg)
            ln, col = (int(m.group(1)), int(m.group(2))) if m else (0, 0)
            if wrap == "body":
                ln, col = ln - 1, col - 4
            tried.append(((ln, col), wrap, msg))
        tried.sort(key=lambda t: t[0], reverse=True)
        return "disagrees-refuses", "parse error: " + "; ".join(
            "%s: %s" % (w, msg) for _, w, msg in tried)
    path = os.path.join(d, c.programs[0][0] + ".verse")
    r = results[path]
    if c.form == "assert_syntax_error":
        ok, msg = parsed[os.path.join(d, "top.verse")]
        body_ok, _ = parsed[os.path.join(d, "body.verse")]
        if not ok:
            return "agrees", "refused (parse%s): %s" % (
                "; parses as a function body" if body_ok else "", msg)
    if "internal" in r:
        return "internal-error", r["internal"]
    rc = r["rc"]
    if rc == 4:
        ok, msg = parsed[path]
        kind = refusal_kind("elab" if ok else "parse", r["diag"])
        if c.expect == "error":
            return "agrees", "refused (%s): %s" % (kind, r["diag"])
        return "disagrees-refuses", "refused (%s): %s" % (kind, r["diag"])
    outcome = {0: "succeeded", 1: "failed", 2: "runtime error", 3: "resource limit"}[rc]
    shown = first_line(r["err"])
    if c.expect == "error":
        return "disagrees-accepts", "accepted (%s)" % outcome
    if c.expect == "valid":
        return "agrees", "accepted"
    if c.expect == "succeeds":
        if rc == 0:
            return "agrees", "succeeded"
        return "wrong-output", "%s: %s" % (outcome, shown)
    if c.expect == "runtime-error":
        if rc in (2, 3):
            return "agrees", "%s: %s" % (outcome, shown)
        return "wrong-output", outcome
    if c.expect == "runs":
        # (a runtime error, here as for `runtime-error`, may be a resource limit)
        if rc in (0, 2, 3):
            return "agrees", outcome
        return "wrong-output", outcome
    return "internal-error", "harness: no expectation"


def run_cases(book, work, jobs, only=None, quiet=False):
    cases = all_cases(book, only)
    os.makedirs(work, exist_ok=True)
    write_programs(work, cases)
    todo = []     # programs to compile and run
    parse = []    # programs to parse
    for c in cases:
        if c.nt:
            continue
        d = case_dir(work, c.id)
        for k, (wrap, _) in enumerate(c.programs):
            p = os.path.join(d, wrap + ".verse")
            parse.append(p)
            if c.expect != "parses" and k == 0:
                todo.append(p)
    if not quiet:
        print("%d cases, %d programs to run, %d to parse" % (len(cases), len(todo), len(parse)),
              file=sys.stderr)
    parsed = parse_only(work, parse, jobs)
    results = {}
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for p, r in zip(todo, ex.map(run_program, todo)):
            results[p] = r
    rows = []
    for c in cases:
        v, detail = verdict(c, results, parsed, work)
        progs = dict(c.programs)
        text = progs.get("top") if c.expect in ("parses", "error") and "top" in progs else \
            (c.programs[0][1] if c.programs else "")
        if c.expect == "parses" and detail.startswith("parse error: body"):
            text = progs["body"]
        if c.form == "assert_syntax_error" and v == "disagrees-accepts":
            text = progs.get("full", text)
        c.cause = causes.cause(c, v, detail, text)
        rows.append((c, v, detail))
    return rows


# ---------------------------------------------------------------------------
# Reports, baseline and comparison.
# ---------------------------------------------------------------------------


def clean(s):
    return re.sub(r"\s+", " ", s).strip()


def write_results(rows, path):
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("id\tform\texpect\ttags\tverdict\tcause\tdetail\n")
        for c, v, detail in rows:
            fh.write("\t".join([c.id, c.form, c.expect or "-", ",".join(c.tags) or "-", v,
                                c.cause or "-", clean(detail)]) + "\n")


def totals(rows):
    """{file: Counter of verdicts}"""
    import collections
    per = collections.OrderedDict()
    for c, v, _ in rows:
        per.setdefault(c.file, collections.Counter())[v] += 1
    return per


def print_totals(rows, out=sys.stdout):
    import collections
    per = totals(rows)
    allc = collections.Counter()
    for k in per.values():
        allc.update(k)
    short = ["agree", "dis-acc", "dis-ref", "wrong", "n/t", "int"]
    out.write("%-70s %6s " % ("file", "cases") + " ".join("%7s" % s for s in short) + "\n")
    for f, k in per.items():
        out.write("%-70s %6d " % (f[len("Tests/"):], sum(k.values())) +
                  " ".join("%7d" % k[v] for v in VERDICTS) + "\n")
    out.write("%-70s %6d " % ("TOTAL", sum(allc.values())) +
              " ".join("%7d" % allc[v] for v in VERDICTS) + "\n")


def print_causes(rows, out=sys.stdout):
    import collections
    per = collections.Counter((v, c.cause) for c, v, _ in rows if c.cause)
    for (v, cause), n in sorted(per.items(), key=lambda kv: (kv[0][0], -kv[1], kv[0][1])):
        out.write("%-18s %-28s %5d\n" % (v, cause, n))


def write_baseline(rows, path):
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("# Book of Verse test conformance baseline: one case per line, its verdict.\n")
        fh.write("# Book revision %s; regenerate with\n" % PINNED)
        fh.write("#   scripts/book-conformance.sh baseline BOOK\n")
        for c, v, _ in rows:
            fh.write("%s\t%s\n" % (c.id, v))


def read_baseline(path):
    base = {}
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            if line.startswith("#") or not line.strip():
                continue
            cid, v = line.rstrip("\n").split("\t")
            base[cid] = v
    return base


DANGEROUS = {"disagrees-accepts", "wrong-output", "internal-error"}


def compare(rows, base):
    """(worse, better, changed, new, gone) lists of (id, old, new, detail)."""
    worse, better, changed, new = [], [], [], []
    now = {}
    for c, v, detail in rows:
        now[c.id] = v
        old = base.get(c.id)
        if old is None:
            new.append((c.id, None, v, detail))
        elif old == v:
            continue
        elif v == "agrees":
            better.append((c.id, old, v, detail))
        elif old == "agrees" or (v in DANGEROUS and old not in DANGEROUS):
            worse.append((c.id, old, v, detail))
        else:
            changed.append((c.id, old, v, detail))
    gone = [(cid, v, None, "") for cid, v in base.items() if cid not in now]
    return worse, better, changed, new, gone


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("command", choices=["run", "compare", "baseline", "show"])
    ap.add_argument("book", help="root of a Book of Verse checkout")
    ap.add_argument("case", nargs="?", help="for show: the case identifier")
    ap.add_argument("--work", default=None, help="work directory (default: a new temporary one)")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--only", default=None, help="only files whose path contains this")
    ap.add_argument("--results", default=None, help="write per-case results (TSV) here")
    ap.add_argument("--baseline", default=BASELINE)
    ap.add_argument("--causes", action="store_true", help="also print the counts by cause")
    a = ap.parse_args()
    book = os.path.abspath(a.book)
    if not os.path.isdir(os.path.join(book, "Tests")):
        sys.exit("%s has no Tests directory" % book)
    rev = subprocess.run(["git", "-C", book, "rev-parse", "HEAD"], stdout=subprocess.PIPE,
                         stderr=subprocess.DEVNULL).stdout.decode().strip()
    if rev and rev != PINNED:
        print("warning: the checkout is at %s, not the pinned %s" % (rev, PINNED), file=sys.stderr)
    if a.command == "show":
        for c in all_cases(book, a.case.split(":")[0]):
            if c.id == a.case:
                print("# %s %s expect=%s tags=%s codes=%s %s" % (c.id, c.form, c.expect,
                      ",".join(c.tags), c.codes, ("not translatable: " + c.nt) if c.nt else ""))
                for wrap, text in c.programs:
                    print("# --- %s.verse" % wrap)
                    print(text)
                return 0
        sys.exit("no case %s" % a.case)
    for tool in (OPENVERSE, CVERSE):
        if not os.access(tool, os.X_OK):
            sys.exit("%s is missing: run `lake build` and `make -C runtime` first" % tool)
    tmp = None
    work = a.work
    if work is None:
        tmp = work = tempfile.mkdtemp(prefix="booktests-")
    try:
        rows = run_cases(book, os.path.abspath(work), a.jobs, a.only)
    finally:
        if tmp:
            shutil.rmtree(tmp, ignore_errors=True)
    if a.results:
        write_results(rows, a.results)
    print_totals(rows)
    if a.causes:
        print_causes(rows)
    if a.command == "baseline":
        if a.only:
            sys.exit("baseline: refusing to write a baseline of a subset (--only)")
        write_baseline(rows, a.baseline)
        print("wrote %s" % a.baseline)
    if a.command == "compare":
        base = read_baseline(a.baseline)
        if a.only:
            ids = {c.id for c, _, _ in rows}
            base = {k: v for k, v in base.items() if k in ids}
        worse, better, changed, new, gone = compare(rows, base)
        for title, lst in (("WORSE", worse), ("BETTER", better), ("CHANGED", changed),
                           ("NEW", new), ("GONE", gone)):
            for cid, old, v, detail in lst:
                print("%s %s: %s -> %s %s" % (title, cid, old, v, clean(detail)[:200]))
        print("compare: %d worse, %d better, %d changed, %d new, %d gone" % (
            len(worse), len(better), len(changed), len(new), len(gone)))
        return 1 if worse else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
