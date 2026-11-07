#!/usr/bin/env openverse run
# Items from the spec draft's mutation syntax, macros and tooling (#25).
# The first line is a shebang, which is a `#` comment.

score := struct:
    Best:?int = false
    Tags:[string]?int = map{}

Main():void =
    # set X? = v sets the value inside an option, and fails when it is empty
    var O:?int = option{1}
    if (set O? = 5, V := O?) then Print("O holds {V}")
    if (set O? += 10, V := O?) then Print("O holds {V}")
    var E:?int = false
    if (set E? = 1) then Print("unreachable") else Print("E is empty, so set E? fails")
    # also as a step of a path
    var S:score = score{Best := option{3}}
    if (set S.Best? *= 7, B := S.Best?) then Print("best {B}")
    set S.Tags["a"] = option{1}
    if (set S.Tags["a"]? += 1, T := S.Tags["a"], U := T?) then Print("tag a {U}")
    if (set S.Tags["b"]? = 1) then Print("unreachable") else Print("no tag b")
    # let(defs){body}: the definitions are visible in the body only
    X := let(A := 6; B := 7) { A * B }
    Print("let gives {X}")
    Y := let(Z := X + 1):
        Z * 2
    Print("and {Y}")
    # the shell arguments
    Print("{Args.Length} argument(s): {Args[0] or "none"}")
