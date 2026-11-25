# (#724) Where an omitted default runs among an archetype's given values is
# not recorded for Epic's Verse VM (differential/cls-construction-order and
# struct-archetype-order give every field), so it is kept: a default runs at
# its field's place in declaration order, and the fields given take, in the
# order written, the places the given fields have. An archetype written in
# declaration order runs as it did. (--extended-defaults: a default that
# prints, to see the order.)
Note(S:string, V:int)<transacts>:int =
    Print("value {S}")
    V

quad := struct:
    A:int = Note("default a", 10)
    B:int
    C:int = Note("default c", 30)
    D:int

quad_cls := class:
    A:int = Note("default a", 10)
    B:int
    C:int = Note("default c", 30)
    D:int
    block:
        Print("block {A} {B} {C} {D}")

Main():void =
    # D's value, written first, runs at B's place; B's at D's
    Q := quad{D := Note("d", 4), B := Note("b", 2)}
    Print("done {Q.A} {Q.B} {Q.C} {Q.D}")
    Q2 := quad{B := Note("b", 2), D := Note("d", 4)}
    Print("done {Q2.A} {Q2.B} {Q2.C} {Q2.D}")
    Q3 := quad{D := Note("d", 4), C := Note("c", 3), B := Note("b", 2), A := Note("a", 1)}
    Print("done {Q3.A} {Q3.B} {Q3.C} {Q3.D}")
    O := quad_cls{D := Note("d", 4), B := Note("b", 2)}
    Print("done {O.A} {O.B} {O.C} {O.D}")
