# logic values: query, not, and, or, and logic{} of each, as values.
# Tests LANGUAGE.md, Supported, Operators: "and (...), or, not (below the
# comparisons, above and ...)"; Readings, "X? of a logic" (settled: the
# empty value) used here only for success and failure. Each letter: t the
# logic is true, f false.
# OpenVerse prints (Lean and C agree):
#   and t f or t f | not t f t | mixed t f t | eq t t t
TF(L:logic):string = if (L?) then "t" else "f"

Main():void =
    T:logic = true
    F:logic = false
    Print("OVPROBE and {TF(logic{T? and T?})} {TF(logic{T? and F?})} or {TF(logic{F? or T?})} {TF(logic{F? or F?})}")
    Print("OVPROBE not {TF(logic{not F?})} {TF(logic{not T?})} {TF(logic{not (T? and F?)})}")
    Print("OVPROBE mixed {TF(logic{T? or F? and F?})} {TF(logic{not 1 = 2 and 1 = 2})} {TF(logic{not 1 = 1 or 2 = 2})}")
    Print("OVPROBE eq {TF(logic{T = true})} {TF(logic{F = false})} {TF(logic{T <> F})}")
