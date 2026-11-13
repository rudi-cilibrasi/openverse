"""Causes of the Book test verdicts that are not agreements.

`cause(case, verdict, detail, program)` names the first rule below that a case
matches. A rule looks at openverse's diagnostic (`detail`), at the line of the
program the diagnostic points to, and at the program itself; rules for
accepted programs and wrong output look at the test's expected error code and
its source. The order matters: specific rules come first. The causes are
described in docs/research/book-test-conformance.md.
"""

import re

# (cause, verdicts it applies to, predicate over a Ctx)
RULES = []


def rule(cause, verdicts, diag=None, line=None, prog=None, code=None, file=None, form=None):
    def test(x):
        if diag and not re.search(diag, x.diag):
            return False
        if line and not re.search(line, x.line):
            return False
        if prog and not re.search(prog, x.prog, re.M):
            return False
        if code and not re.fullmatch(code, x.code):
            return False
        if file and not re.search(file, x.file):
            return False
        if form and not re.fullmatch(form, x.form):
            return False
        return True
    RULES.append((cause, verdicts, test))


REF = ("disagrees-refuses",)
ACC = ("disagrees-accepts",)
OUT = ("wrong-output",)

# --- programs openverse accepts that the tests refuse, by expected error code
rule("cyclic-initializers", ACC, code="3502", file=r"CyclicReferences|DefaultValueAssignment|ModuleDefinitions")
for codes, cause in [
        ("3514|3547", "reserved-names"),
        ("3593|3594|3543|3650|3642", "access-specifiers"),
        ("3596|3680", "misplaced-specifiers"),
        ("3519", "concrete-classes"),
        ("3673|3568|3674|3591", "final-members"),
        ("3532", "duplicate-definitions"),
        ("9200|9000|9002|3655", "name-limits"),
        ("2000|2302|3535|3616|2002", "unreachable-code"),
        ("3554", "float-literal-range"),
        ("3565", "class-effects"),
        ("3662", "persistable"),
        ("3678", "castable"),
        ("3582|9003", "initializer-effects"),
        ("3567", "defer-placement"),
        ("3588", "overload-ambiguity"),
        ("3592|3523", "interface-rules"),
        ("2003|2004|3506|3612", "qualified-names"),
        ("3502", "epic-limits"),
        ("3512|3513", "effect-checks"),
        ("3524|3544|3534|3579|3538|3548", "control-forms"),
        ]:
    rule(cause, ACC, code=codes)
rule("comment-lexing", ACC, form="assert_syntax_error", file=r"TimSyntax")
rule("syntax-other", ACC, form="assert_syntax_error")
rule("type-checks-other", ACC)

# --- different output
rule("int-precision", OUT, diag=r"overflow")
rule("empty-values-equal", OUT, prog=r"(Y:(void|logic|tuple\(\)|\?int|\[\]int|\[int\]int|string)\s*=\s*"
     r"(\{\}|false|\(\)|array\{\}|map\{\}|\"\"))|\(\)\s*=\s*\"\"|\"\"\s*=\s*\(\)|X:void\s*=|true\?\s*\??|"
     r"X\s*=\s*\(\)$|\(true\? and true\?\) = false|true\?\s+or true")
rule("compound-set-order", OUT, prog=r"set [^\n]*\+= if \(set ")
rule("comma-sequences", OUT, prog=r"\)\s*\{\s*\w+\s*,\s*\w+\s*\}\s*=|option\{1,2\}|^\s+1; 2; 3$")
rule("comparison-chains", OUT, prog=r"not\s+1 <>\s+2\s+<> 1")
rule("for-rollback", OUT, file=r"FlowControl/for|Range\.|SoftwareTransactionalMemory")
rule("map-concat-order", OUT, file=r"ConcatenateMaps")
rule("float-to-string", OUT, file=r"FloatToString")
rule("comments-in-strings", OUT, prog=r'"[^"\n]*<#')
rule("output-other", OUT)

# --- refusals: first by openverse's diagnostic, where it names the feature
K = r"(?:class|struct|module|interface|enum|union|scoped|type)\b"
rule("override-defaults", REF, diag=r"must give a new default|must have the type it inherits|"
     r"must have the signature of")
rule("partial-modules", REF, diag=r"module \S+ is defined twice")
rule("empty-containers", REF, diag=r"the type of an empty (array|map)")
rule("comparisons", REF, diag=r"compares values of different types|no operator '(=|<>)'|"
     r"expected string, found tuple")
rule("joins", REF, diag=r"the branches have different types|values of this (map|array) have different "
     r"types|elements of this array")
rule("variance", REF, diag=r"expected \w*(variant|bivariant)\w*\(")
rule("spawn-in-failure-context", REF, diag=r"spawn cannot be in a failure context")
rule("module-objects", REF, diag=r"would hold an object with var fields or of a <unique> class")
rule("effects-of-classes", REF, diag=r"that class/interface also has")
rule("ranges", REF, diag=r"a range a\.\.b can only be")
rule("set-forms", REF, diag=r"openverse supports set X = |expected '=' or a compound assignment in set")
rule("char-literals", REF, diag=r"char literal must")
rule("float-literals", REF, diag=r"a float literal is")
rule("weak-map", REF, diag=r"weak_map")
rule("library-bitwise", REF, diag=r"unknown function 'Bit")
rule("library-chars", REF, diag=r"unknown function 'ToChar|char32? has no method")
rule("library-diagnostic", REF, diag=r"ToDiagnostic|diagnosable")
rule("library-other", REF, diag=r"unknown (function|identifier) '(Clamp|Sgn|GetCastableFinalSuperClass\w*|"
     r"GetSecondsSinceEpoch|FitsInPlayerMap|Sin|Cos|Tan|Sinh|Cosh|Tanh|Exp|Ln|Sqrt|ArcSin|ArcCos|ArSinh|"
     r"ArCosh|ArTanh|Pow2_\w+)'|(int|float|string|tuple\([^)]*\)) has no method")
rule("structural-types", REF, diag=r"unknown (type|function) 'comparable'")
rule("metatypes", REF, diag=r"unknown parametric type '(subtype|castable_subtype|concrete_subtype|"
     r"castable_concrete_subtype|classifiable_subset)'|unknown type 'type'|unknown (function|identifier) "
     r"'(int|float|void|tuple|class\w*|interface\w*|s|c|t|C|Self|concrete_class)'|unknown type 't'")
rule("localization", REF, diag=r"<localizes>|unknown type 'message'")
rule("closed-functions", REF, diag=r"<closed>")
rule("comparable-classes", REF, diag=r"must be comparable, and .* is a class")
rule("singleton-types", REF, diag=r"unknown type '(true|false)'")
rule("impossible-casts", REF, diag=r"so \S+\[…\] would always fail")
rule("subtyping-to-any", REF, diag=r"expected [^,]*\bany\b[^,]*, found|cannot concatenate|"
     r"an operand of '=' must be comparable, and any")
rule("class-specifiers", REF, diag=r"<final_super>|<persistable>|<castable>|<unique>|<concrete>|"
     r"specifier|not supported yet|is unsupported")
rule("generators", REF, diag=r"unknown parametric type 'generator'|'generator'")
# --- then by the source line a parse error points to
rule("unnamed-parameters", REF, diag=r"expected an identifier, found ':'")
rule("unnamed-parameters", REF, line=r"[(,]\s*:\s*[A-Za-z_?\[(]", diag=r"\(parse\)")
rule("extension-methods", REF, line=r"^\s*\([A-Za-z_]*\s*:[^()]*(\([^()]*\))?[^()]*\)\s*\.\s*[A-Za-z_]")
rule("qualified-names", REF, line=r"\((local|super|[A-Za-z_][\w.]*|/[^:)]*):\)\s*[A-Za-z_]")
rule("qualified-names", REF, diag=r"is not a class or interface above|only a method can be qualified|"
     r"qualified method")
rule("nested-tuple-parameters", REF, diag=r"expected an identifier, found '\('")
rule("path-literals", REF, line=r"^\s*/[A-Za-z0-9]|import\s*\(|\(/[A-Za-z]")
rule("attributes", REF, diag=r"unexpected character '@'")
rule("attributes", REF, prog=r"^\s*@[a-z_]", diag=r"\(parse\)|parse error")
rule("attributes", REF, line=r"<[a-z_]+\(")
rule("var-specifiers", REF, line=r"\bvar\s*<|<getter\(|<setter\(")
rule("live-variables", REF, line=r"\b(live|when|upon|await|batch)\b")
rule("union-types", REF, line=r"\bunion\b")
rule("type-aliases", REF, diag=r"a constant in a module needs its type")
rule("type-aliases", REF, line=r"^\s*[A-Za-z_]\w*\s*:=\s*(\?|\[|type\s*\{|tuple\(|int\b|float\b|string\b|"
     r"logic\b|[a-z_]\w*\s*->|subtype\(|[a-z_]\w*\s*$)")
rule("metatypes", REF, line=r"\b(subtype|castable_subtype|concrete_subtype|castable_concrete_subtype)\s*\(|"
     r"\btype\s*\{_|\bt\s*:\s*type\b")
rule("path-literals", REF, line=r"import\s*\(|(^|[\s(={,])/[A-Za-z]")
rule("operator-definitions", REF, line=r"(operator|prefix|postfix)'")
rule("empty-bodies", REF, diag=r"expected the indented body of|expected an indented method body|"
     r"expected the struct's fields|expected an indented function body|expected an indented block|"
     r"unexpected indentation")
rule("if-without-then", REF, diag=r"expected 'then'", line=r"^\s*(if|else)\b|^\s*\S")
rule("dot-forms", REF, line=r"(\b(if|for|then|else|array|spawn|block|loop)|\))\s*\.\s")
rule("block-forms", REF, line=r"\b(spawn|branch|profile|for|option|array|map|block|sync|race|rush|case|"
     r"loop|defer)\s*:\s*$")
rule("block-forms", REF, diag=r"has no body: its value is its last clause")
rule("archetype-blocks", REF, line=r"(:=|=)\s*(?!%s)[a-z_][\w.]*(\([^)]*\))?\s*:\s*$" % K)
rule("first-forms", REF, line=r"\bfirst\s*[({]")
rule("named-tuple-elements", REF, line=r"\(\s*[^()]*,\s*\?[A-Za-z_]\w*\s*:=")
rule("type-conversions", REF, line=r"\b(logic|int|float|string)\s*\(|\(\s*(\[\]|\?)[a-z]+\s*\)\s*\(")
rule("function-parameters", REF, line=r"\w\([A-Za-z_]\w*\([^)]*\(", diag=r"expected ':'")
rule("nested-functions", REF, line=r"=>|<closed>")
rule("nested-functions", REF, diag=r"a definition in a module must start")
rule("archetype-separators", REF, diag=r"expected ',' or '\}'|expected ';', a new line or '\}'")
rule("empty-parentheses", REF, diag=r"expected a type, found '\)'")
rule("syntax-other", REF, diag=r"\(parse\)|parse error")
rule("types-other", REF)
rule("internal-error", ("internal-error",))


class Ctx:
    def __init__(self, case, verdict, detail, program):
        self.case = case
        self.diag = detail
        self.file = case.file
        self.form = case.form
        self.code = case.codes.replace(" ", "").split(",")[0] if case.codes else ""
        self.code = re.sub(r"<#[^#]*#>", "", self.code)
        self.prog = program or ""
        self.line = ""
        m = re.search(r"(\d+):(\d+): ", detail)
        if m and program:
            lines = program.split("\n")
            k = int(m.group(1))
            if 0 < k <= len(lines):
                self.line = lines[k - 1]


def cause(case, verdict, detail, program):
    """The cause of a verdict other than agrees and not-translatable, or ""."""
    if verdict in ("agrees", "not-translatable"):
        return ""
    x = Ctx(case, verdict, detail, program)
    for name, verdicts, test in RULES:
        if verdict in verdicts and test(x):
            return name
    return "unclassified"
