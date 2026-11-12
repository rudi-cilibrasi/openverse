#!/usr/bin/env python3
"""Source-loop model for for filters: break crosses producers; failure rolls back.

Some consumers select their lazy sources under independent
refining casts. Both actual receivers hit, so the source-loop oracle and
the existing random program distribution stay unchanged, including waits.
Plain, composed and exclusive wrappers enumerate the same lazy values.
--unrefined emits the equivalent original sources for implementation controls.
--plain-sources/--composed-sources/--exclusive-sources select that emitter profile.
--first-success instead models a break in the clauses of an if condition,
first{} or option{} with choices (first_success below).
"""
import random
import sys
from pathlib import Path


def first_success(seed, expected):
    """A loop whose body takes the first success of clauses with choices,
    with a break among them (#283). The search is depth first: each
    alternative starts from the state where its choice was reached, so one
    that fails is rolled back, and so is the whole context when none
    succeeds (output too: Print is transactional). An effectful recursive
    generator (Visit) is a choice of its value and a call of itself, after
    its own clauses, as the Verse Calculus reads it. A break keeps what the
    clauses did up to it, as with no choice, and leaves the loop: the
    cleanup of the scopes it leaves runs (a block's, then the loop's). A
    block's defer: runs as each of its values leaves it, and at a break or
    return that leaves it (after the return's value), whether the block has
    a choice of its own, which lifts its clauses into the condition's, or
    not: LANGUAGE.md's rule for any scope. A return leaves the function,
    running the cleanup of every scope it leaves, innermost first."""
    rng = random.Random(seed)
    suspends = rng.choice([False, True])
    waits = suspends and rng.choice([False, True])
    nested = rng.choice([False, True])
    form = rng.choice(["if", "first", "option", "for"])
    reps = rng.randint(1, 3)
    outer_reps = rng.randint(1, 2) if nested else 1
    loop_delta, fn_delta = rng.randint(1, 7), rng.randint(1, 7)
    loop_vars = ["K", "J"] if nested else ["K"]

    # (an expression: a sum of names and a constant, as text and as a value)
    def expr(names, const):
        text = " + ".join(names) if names else str(const)
        if names and const > 0:
            text += f" + {const}"
        if names and const < 0:
            text += f" - {-const}"
        return text, lambda env: sum(env[n] for n in names) + const

    def pick_expr(bound):
        names = rng.sample(bound, k=min(len(bound), rng.randint(1, 2)))
        return expr(names, rng.randint(-1, 2) if names else rng.randint(0, 4))

    ops = {"=": lambda a, b: a == b, "<>": lambda a, b: a != b, "<": lambda a, b: a < b,
           ">": lambda a, b: a > b, "<=": lambda a, b: a <= b, ">=": lambda a, b: a >= b}

    # (a comparison of the names bound so far with a constant, or, for a
    # break, often with the iteration, so that iterations differ)
    def pick_pred(bound, iteration=False):
        lt, lv = pick_expr(bound)
        op = rng.choice(["=", "=", "<>", "<", ">", "<=", ">="])
        if iteration and rng.random() < 0.6:
            rt, rv = expr(rng.sample(loop_vars, k=rng.randint(1, len(loop_vars))), rng.randint(-1, 3))
        else:
            rt, rv = expr([], rng.randint(0, 6))
        return f"{lt} {op} {rt}", lambda env: ops[op](lv(env), rv(env))

    # The choices: Verse text, and the values (with Visit's effects, its
    # own search). `refined` choices need the generic Run's receiver P.
    refined = [False]

    def plain_values(vals):
        def gen(env, st, k):
            for v in vals(env):
                r = k(v, st.copy())
                if r[0] != "fail":
                    return r
            return ("fail",)
        return gen

    def pick_choice(i, bound):
        kind = rng.choice(["plain", "plain", "two", "composed", "exclusive", "lazy", "visit", "refined"])
        if kind == "plain":
            vs = [rng.randint(0, 5) for _ in range(rng.randint(2, 3))]
            return " | ".join(map(str, vs)), plain_values(lambda env: vs)
        if kind == "two":
            a = rng.randint(0, 4)
            return f"Two({a})", plain_values(lambda env: [a, a + 1])
        if kind == "composed":
            a, b = rng.randint(0, 3), rng.randint(0, 4)
            return f"(Two({a}) | Two({b}))", plain_values(lambda env: [a, a + 1, b, b + 1])
        if kind == "exclusive":
            n = rng.randint(-1, 4)
            return f"Early({n})", plain_values(lambda env: [0] if n < 0 else [n, n + 1])
        if kind == "lazy":
            if bound and rng.random() < 0.4:
                at, av = expr([rng.choice(bound)], rng.randint(-1, 1))
            else:
                at, av = expr([], rng.randint(-1, 3))
            return f"Lazy[{at}]", plain_values(lambda env: list(range(av(env), -1, -1)))
        if kind == "refined":
            refined[0] = True
            return (f"(if (D{i} := dup[P]) then (D{i}.C | D{i}.C + 1) else 0)",
                    plain_values(lambda env: [refined_c, refined_c + 1]))
        a = rng.randint(0, 2)
        b = a + rng.randint(-1, 3)

        def visit(env, st, k):
            def call(x, st):
                if x > b:
                    return ("fail",)
                st = st.copy()
                st.hn += 1
                st.out.append(f"visit {x} {st.hn}")
                r = k(x, st.copy())
                if r[0] != "fail":
                    return r
                return call(x + 1, st)
            return call(a, st)
        return f"Visit[H, {a}, {b}]", visit

    refined_c = rng.randint(0, 4)

    class St:
        def __init__(self, total=0, hn=0, out=None):
            self.total, self.hn, self.out = total, hn, out if out is not None else []

        def copy(self):
            return St(self.total, self.hn, list(self.out))

    # The clauses, each as (text, step): a step takes the environment, the
    # state and the rest of the search, and gives its outcome.
    clauses = []
    bound = []
    n_choices = rng.randint(1, 3)
    n_breaks = rng.choice([0, 1, 1, 1, 2])
    plan = ["choice"] * n_choices + ["break"] * n_breaks + ["filter"] + \
        [rng.choice(["total", "hn", "print", "filter", "block"]) for _ in range(rng.randint(1, 4))]
    rng.shuffle(plan)
    for i, what in enumerate(plan):
        if what == "choice":
            name = f"X{i}"
            text, gen = pick_choice(i, bound)
            clauses.append((f"{name} := {text}",
                            lambda env, st, rest, name=name, gen=gen:
                            gen(env, st, lambda v, st2: rest({**env, name: v}, st2))))
            bound.append(name)
        elif what in ("total", "hn"):
            et, ev = pick_expr(bound)
            target = "Total" if what == "total" else "H.N"

            def step(env, st, rest, what=what, ev=ev):
                if what == "total":
                    st.total += ev(env)
                else:
                    st.hn += ev(env)
                return rest(env, st)
            clauses.append((f"set {target} += {et}", step))
        elif what == "print":
            shown = list(bound)

            def step(env, st, rest, i=i, shown=shown):
                st.out.append(" ".join([f"p{i}"] + [str(env[n]) for n in shown] + [str(st.total), str(st.hn)]))
                return rest(env, st)
            clauses.append(("Print(\"" + " ".join([f"p{i}"] + ["{" + n + "}" for n in shown] + ["{Total}", "{H.N}"]) + "\")",
                            step))
        elif what == "filter":
            pt, pv = pick_pred(bound, iteration=not bound)
            clauses.append((pt, lambda env, st, rest, pv=pv: rest(env, st) if pv(env) else ("fail",)))
        elif what == "break":
            if rng.random() < 0.15:
                clauses.append(("break", lambda env, st, rest: ("break", st)))
            else:
                pt, pv = pick_pred(bound, iteration=True)
                clauses.append((f"if ({pt}) then break else 0",
                                lambda env, st, rest, pv=pv: ("break", st) if pv(env) else rest(env, st)))
        else:
            # (a block of its own, with a defer: that a break or return leaving
            # it runs; at times with a choice of its own, W, before or after
            # the defer:, then each of its values leaves the block in turn)
            name = f"Z{i}"
            own = rng.random() < 0.6
            inner = list(bound)
            if own:
                w = f"W{i}"
                ctext, cgen = pick_choice(i, bound)
                inner.append(w)
            pt, pv = pick_pred(inner, iteration=True)
            vt, vv = pick_expr(inner)
            ret = rng.random() < 0.35
            if ret:
                rt, rv = pick_expr(inner)

            def leave(env, st, rest, i=i, name=name, pv=pv, vv=vv, ret=ret, rv=rv if ret else None):
                if pv(env):
                    # (a return's value first, then the block's cleanup)
                    value = rv(env) if ret else None
                    st.out.append(f"bd{i} {st.total} {st.hn}")
                    return ("return", st, value) if ret else ("break", st)
                v = vv(env)
                st.out.append(f"bd{i} {st.total} {st.hn}")
                return rest({**env, name: v}, st)
            stmts = [f"defer: Print(\"bd{i} {{Total}} {{H.N}}\")"]
            if own:
                stmts.insert(rng.randint(0, 1), f"{w} := {ctext}")

                def step(env, st, rest, w=w, cgen=cgen, leave=leave):
                    return cgen(env, st, lambda v, st2: leave({**env, w: v}, st2, rest))
            else:
                step = leave
            exit_text = f"return {rt}" if ret else "break"
            clauses.append((f"{name} := block{{ {'; '.join(stmts)}; if ({pt}) then {exit_text}; {vt} }}", step))
            bound.append(name)
    first_choice = next(n for n in bound if n.startswith("X"))

    def search(env, st, j=0):
        if j == len(clauses):
            return ("ok", env, st)
        return clauses[j][1](env, st, lambda env2, st2: search(env2, st2, j + 1))

    # The run, as the program does it.
    st = St()
    J = 0
    returned = None
    while True:
        J += 1
        K = 0
        while True:
            r = search({"K": K, "J": J}, st.copy())
            if r[0] == "return":
                # (it leaves the loops, each running its cleanup, then the function)
                st, returned = r[1], r[2]
                st.total += loop_delta
                st.hn += loop_delta
                st.out.append(f"loop cleanup {K} {st.total} {st.hn}")
                if nested:
                    st.out.append(f"outer cleanup {J} {st.total} {st.hn}")
                break
            if r[0] == "break":
                st = r[1]
            elif form == "for":
                if r[0] == "ok":
                    st = r[2]
                st.out.append(f"for {1 if r[0] == 'ok' else 0} {st.total} {st.hn}")
            elif r[0] == "ok":
                st = r[2]
                shown = bound if form == "if" else [first_choice]
                st.out.append(" ".join(["then"] + [str(r[1][n]) for n in shown] + [str(st.total), str(st.hn)]))
            else:
                st.out.append(f"else {st.total} {st.hn}")
            if r[0] != "break":
                K += 1
            st.total += loop_delta
            st.hn += loop_delta
            st.out.append(f"loop cleanup {K} {st.total} {st.hn}")
            if r[0] == "break" or K >= reps:
                break
        if not nested or returned is not None:
            break
        st.out.append(f"outer {J} {K}")
        st.out.append(f"outer cleanup {J} {st.total} {st.hn}")
        if J >= outer_reps:
            break
    answer = st.total if returned is None else returned
    st.total += fn_delta
    st.hn += fn_delta
    st.out.append(f"function cleanup {st.total} {st.hn}")
    st.out.append(f"result {answer} {st.hn}")
    Path(expected).write_text("exit=0\n" + "".join(line + "\n" for line in st.out))

    # The program.
    texts = [t for t, _ in clauses]
    then_shown = bound if form == "if" else ["R"]
    then = 'Print("' + " ".join(["then"] + ["{" + n + "}" for n in then_shown] + ["{Total}", "{H.N}"]) + '")'
    ind = "            " if nested else "        "
    if form == "if":
        consumer = f"if ({', '.join(texts)}):\n{ind}    {then}\n{ind}else:\n{ind}    Print(\"else {{Total}} {{H.N}}\")"
    elif form == "first":
        consumer = (f"if (R := first{{{'; '.join(texts)}; {first_choice}}}):\n{ind}    {then}\n"
                    f"{ind}else:\n{ind}    Print(\"else {{Total}} {{H.N}}\")")
    elif form == "option":
        consumer = (f"Opt := option{{{'; '.join(texts)}; {first_choice}}}\n{ind}if (R := Opt?):\n{ind}    {then}\n"
                    f"{ind}else:\n{ind}    Print(\"else {{Total}} {{H.N}}\")")
    else:
        # (in a for's filters: a source break crosses the for too)
        consumer = (f"for (Y := 0..0, B := (if ({', '.join(texts)}) then 1 else 0)):\n"
                    f"{ind}    Print(\"for {{B}} {{Total}} {{H.N}}\")")
    inner = (f"loop:\n{ind}defer:\n{ind}    set Total += {loop_delta}\n{ind}    set H.N += {loop_delta}\n"
             f"{ind}    Print(\"loop cleanup {{K}} {{Total}} {{H.N}}\")\n"
             + (f"{ind}Sleep(0.0)\n" if waits else "")
             + f"{ind}{consumer}\n{ind}set K += 1\n{ind}if (K >= {reps}):\n{ind}    break")
    if nested:
        body = ("var J:int = 0\n    loop:\n        defer:\n            Print(\"outer cleanup {J} {Total} {H.N}\")\n"
                f"        set J += 1\n        set K = 0\n        {inner}\n        Print(\"outer {{J}} {{K}}\")\n"
                f"        if (J >= {outer_reps}):\n            break")
    else:
        body = inner
    mode = "<suspends>" if suspends else "<transacts>"
    pre = '''cell := class:
    var N:int = 0
Two(N:int):int = N | N + 1
Early(N:int):int =
    if (N < 0):
        return 0
    N | N + 1
Lazy(N:int)<computes><decides>:int =
    N >= 0
    N | Lazy[N - 1]
Visit(H:cell, A:int, B:int)<transacts><decides>:int =
    A <= B
    set H.N += 1
    Print("visit {A} {H.N}")
    A | Visit[H, A + 1, B]
'''
    params, args = "", ""
    if refined[0]:
        pre += "pair(a:type, b:type) := class {}\ndup(t:type) := class(pair(t, t)) { C:int }\n"
        params, args = ", P:pair(a, b) where a:type, b:type", f", dup(int){{C := {refined_c}}}"
    print(pre + f'''Run(H:cell{params}){mode}:int =
    var Total:int = 0
    defer:
        set Total += {fn_delta}
        set H.N += {fn_delta}
        Print("function cleanup {{Total}} {{H.N}}")
    var K:int = 0
    {body}
    Total
Main(){mode}:void =
    H := cell{{}}
    Print("result {{Run(H{args})}} {{H.N}}")
''')


if "--first-success" in sys.argv[3:]:
    first_success(int(sys.argv[1]), sys.argv[2])
    sys.exit(0)

seed = int(sys.argv[1])
rng = random.Random(seed)
na, nb = rng.randint(-1, 3), rng.randint(-1, 3)
cut_a, cut_b = rng.randint(0, 3), rng.randint(0, 3)
refs_a, refs_b = rng.choice([False, True]), rng.choice([False, True])
suspends, used = rng.choice([False, True]), rng.choice([False, True])
waits = suspends and rng.choice([False, True])
refined = bool(seed & 8) and "--unrefined" not in sys.argv[3:]
source_style = ("plain", "composed", "exclusive")[seed % 3]
for style in ("plain", "composed", "exclusive"):
    if f"--{style}-sources" in sys.argv[3:]:
        source_style = style
body_delta, filter_delta, loop_delta, fn_delta = [rng.randint(1, 7) for _ in range(4)]
reachable = [(a, b) for a in range(na, -1, -1) for b in range(nb, -1, -1)
             if a >= cut_a and b >= cut_b]
stop = rng.choice([-1] + [a * 10 + b for a, b in reachable])

# Each real generator begins its own filter snapshot. No producer effects.
total = field = count = 0
out = []
stopped = False
for a in range(na, -1, -1):
    before_a = total, field, len(out)
    total += a
    field += a + 1
    out.append(f"a {a} {total} {field}")
    if a < cut_a:
        total, field, size = before_a
        del out[size:]
        continue
    for b in range(nb, -1, -1):
        before_b = total, field, len(out)
        total += b
        field += b + 1
        out.append(f"b {b} {total} {field}")
        if b < cut_b:
            total, field, size = before_b
            del out[size:]
            continue
        if a * 10 + b == stop:
            total += filter_delta
            field += filter_delta
            out.append(f"filter cleanup {total} {field}")
            stopped = True
            break
        out.append(f"keep {a} {b}")
        total += body_delta
        field += body_delta
        out.append(f"local cleanup {total} {field}")
        out.append(f"body {a} {b} {total} {field}")
        count += 1
    if stopped:
        break
if not stopped:
    out.append(f"completed {count if used else field}")
total += loop_delta
field += loop_delta
out.append(f"loop cleanup {total} {field}")
answer = total
total += fn_delta
field += fn_delta
out.append(f"function cleanup {total} {field}")
out.append(f"result {answer} {field}")
Path(sys.argv[2]).write_text("exit=0\n" + "".join(line + "\n" for line in out))

pre = '''counter := class:
    var N:int = 0
Lazy(N:int)<computes><decides>:int =
    N >= 0
    N | Lazy[N-1]
RefLazy(N:int)<transacts><decides>:counter =
    N >= 0
    counter{N:=N} | RefLazy[N-1]
'''
if source_style == "exclusive":
    pre += '''ExLazy(N:int)<computes><decides>:int =
    if(N<0):return Lazy[N]
    Lazy[N]
ExRefLazy(N:int)<transacts><decides>:counter =
    if(N<0):return RefLazy[N]
    RefLazy[N]
'''
if refined:
    pre += 'pair(a:type,b:type) := class {}\ndup(t:type) := class(pair(t,t)) { C:int }\n'
def source(name, n):
    if source_style == "composed":
        return f"({name}[{n}]|{name}[-1])"
    return f"{'Ex' if source_style == 'exclusive' else ''}{name}[{n}]"

source_a = source('RefLazy' if refs_a else 'Lazy', na)
if refined:
    source_a = f"if(D:=dup[P])then {source('RefLazy' if refs_a else 'Lazy', 'D.C')}else {source_a}"
clauses = [f"{'EA' if refs_a else 'A'} := {source_a}"]
if refs_a:
    clauses.append("A := EA.N")
clauses += ["set Total += A", "set H.N += A + 1", 'Print("a {A} {Total} {H.N}")', f"A >= {cut_a}"]
source_b = source('RefLazy' if refs_b else 'Lazy', nb)
if refined:
    source_b = f"if(E:=dup[Q])then {source('RefLazy' if refs_b else 'Lazy', 'E.C')}else {source_b}"
clauses.append(f"{'EB' if refs_b else 'B'} := {source_b}")
if refs_b:
    clauses.append("B := EB.N")
clauses += ["set Total += B", "set H.N += B + 1", 'Print("b {B} {Total} {H.N}")', f"B >= {cut_b}",
            f'''if (A * 10 + B = {stop}):
                defer:
                    set Total += {filter_delta}
                    set H.N += {filter_delta}
                    Print("filter cleanup {{Total}} {{H.N}}")
                break
            else:
                Print("keep {{A}} {{B}}")''']
body = f'''loop:
                defer: Print("local cleanup {{Total}} {{H.N}}")
                set Total += {body_delta}
                set H.N += {body_delta}
                break
'''
if waits:
    body += '            Sleep(0.0)\n'
body += '            Print("body {A} {B} {Total} {H.N}")\n            (A, B)'
mode = '<suspends>' if suspends else '<transacts>'
loop = ("R := " if used else "") + f"for ({', '.join(clauses)}):\n            {body}"
finish = 'R.Length' if used else 'H.N'
params = ',P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type' if refined else ''
args = f',dup(int){{C:={na}}},dup(string){{C:={nb}}}' if refined else ''
print(pre + f'''Run(H:counter{params}){mode}:int =
    var Total:int = 0
    defer:
        set Total += {fn_delta}
        set H.N += {fn_delta}
        Print("function cleanup {{Total}} {{H.N}}")
    loop:
        defer:
            set Total += {loop_delta}
            set H.N += {loop_delta}
            Print("loop cleanup {{Total}} {{H.N}}")
        {loop}
        Print("completed {{{finish}}}")
        if ({stop} >= 0):
            Err()
        break
    Total
Main(){mode}:void =
    H := counter{{}}
    Print("result {{Run(H{args})}} {{H.N}}")
''')
