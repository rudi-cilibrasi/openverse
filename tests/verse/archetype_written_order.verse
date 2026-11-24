# (#724) The fields an archetype gives are evaluated in the order written,
# as on Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20): differential/cls-construction-order prints `value b` then
# `value a` for derived_cls{B := …, A := …}, then the block: clauses from
# the top, and differential/struct-archetype-order `c`, `a`, `b`. openverse
# evaluated them in declaration order.
# (Where an omitted default runs among the given values:
# archetype_written_order_defaults.)
Note(S:string, V:int):int =
    Print("value {S}")
    V

base_cls := class:
    A:int = 1
    block:
        Print("base block A {A}")

derived_cls := class(base_cls):
    B:int = 2
    block:
        Print("derived block one B {B}")
    block:
        Print("derived block two A {A}")

trio := struct:
    A:int
    B:int
    C:int

pair_cls := class:
    X:int
    Y:string

MakePair<constructor>(N:int) := pair_cls:
    Y := "y{Note("ctor y", N)}"
    X := Note("ctor x", N + 1)

mixed := struct:
    S:string
    F:float
    N:int

NoteT(S:string, V:int)<transacts>:int =
    Print("value {S}")
    V

Pick()<transacts><decides>:int =
    Print("pick")
    7

Main():void =
    D := derived_cls{B := Note("b", 20), A := Note("a", 10)}
    Print("done {D.A} {D.B}")
    T := trio{C := Note("c", 3), A := Note("a", 1), B := Note("b", 2)}
    Print("done {T.A}{T.B}{T.C}")
    # as declared: nothing changes
    T2 := trio{A := Note("a", 1), B := Note("b", 2), C := Note("c", 3)}
    Print("done {T2.A}{T2.B}{T2.C}")
    P := MakePair(5)
    Print("done {P.X} {P.Y}")
    # fields of different types, each value at its own field's type
    M := mixed{N := Note("n", 1), F := 2.5, S := "s{Note("s", 3)}"}
    Print("done {M.S} {M.F} {M.N}")
    # in a failure context too
    if (R := trio{B := NoteT("b", 2), C := Pick[] + 100, A := NoteT("a", 1)}):
        Print("done {R.A}{R.B}{R.C}")
