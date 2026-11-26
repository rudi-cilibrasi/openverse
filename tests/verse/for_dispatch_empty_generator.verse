# (#761) A `for` over a call of an overridden method, or of an interface's
# method, with several values. The call is reached by dispatch on the
# receiver's class: the for picks the implementation, as an `if` picks a
# branch, and that implementation's values are its own choice. A row that
# reaches no body is undone back to the value or element it is in. `Inner`
# adds 100 and gives an element only for V = 1. The controls have the same
# rows from a written choice of values or an array.
Cell := class{var N:int = 0}
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1} else array{}
base := class:
    Vals(S:Cell)<transacts>:int = 4 | 1
derived := class(base):
    Vals<override>(S:Cell)<transacts>:int = 3 | 1
writer := class(base):
    Vals<override>(S:Cell)<transacts>:int =
        set S.N += 10
        5 | 1
shape := interface:
    Sides(S:Cell)<transacts>:int
square := class(shape):
    Sides<override>(S:Cell)<transacts>:int = 3 | 1
triangle := class(shape):
    Sides<override>(S:Cell)<transacts>:int = 5 | 1
gbase(t:type) := class:
    X:t
    Y:t
    Vals(S:Cell)<transacts>:t = X | Y
gderived(t:type) := class(gbase(t)):
    Vals<override>(S:Cell)<transacts>:t = Y | (super:)Vals(S)
# Rows 3, 1 of the override.
Override(S:Cell)<transacts>:void =
    B:base = derived{}
    for (V := B.Vals(S), W : Inner(S, V)):
        Print("override {V} {W} {S.N}")
# Rows 4, 1 of the class's own.
Base(S:Cell)<transacts>:void =
    B:base = base{}
    for (V := B.Vals(S), W : Inner(S, V)):
        Print("base {V} {W} {S.N}")
Control(S:Cell)<transacts>:void =
    for (V := (3 | 1), W : Inner(S, V)):
        Print("control {V} {W} {S.N}")
# The override writes before its values, rows 5 and 1: its 10 is kept with
# the row 1, and the row 5 is undone back to it.
Writes(S:Cell)<transacts>:void =
    B:base = writer{}
    for (V := B.Vals(S), W : Inner(S, V)):
        Print("writes {V} {W} {S.N}")
WritesControl(S:Cell)<transacts>:void =
    for ((set S.N += 10; true?), V := (5 | 1), W : Inner(S, V)):
        Print("writes {V} {W} {S.N}")
# A receiver of each class in turn: rows 3, 1; 4, 1; then 10 and 5, 1.
Each(S:Cell)<transacts>:void =
    Bs:[]base = array{derived{}, base{}, writer{}}
    for (B : Bs, V := B.Vals(S), W : Inner(S, V)):
        Print("each {V} {W} {S.N}")
# An interface's method: rows 3, 1 and 5, 1.
Faces(S:Cell)<transacts>:void =
    Shapes:[]shape = array{square{}, triangle{}}
    for (B : Shapes, V := B.Sides(S), W : Inner(S, V)):
        Print("faces {V} {W} {S.N}")
FacesControl(S:Cell)<transacts>:void =
    for (V : array{3, 1, 5, 1}, W : Inner(S, V)):
        Print("faces {V} {W} {S.N}")
# A generic class's override, which takes the parent's values through
# `(super:)` after its own: rows 3, then 1 and 3.
Super(S:Cell)<transacts>:void =
    B:gbase(int) = gderived(int){X := 1, Y := 3}
    for (V := B.Vals(S), W : Inner(S, V)):
        Print("super {V} {W} {S.N}")
SuperControl(S:Cell)<transacts>:void =
    for (V := (3 | 1 | 3), W : Inner(S, V)):
        Print("super {V} {W} {S.N}")
Run(Name:string, F(:Cell)<transacts>:void)<transacts>:void =
    S := Cell{}
    F(S)
    Print("{Name} state {S.N}")
Main()<transacts>:void =
    Run("override", Override)
    Run("base", Base)
    Run("control", Control)
    Run("writes", Writes)
    Run("writes", WritesControl)
    Run("each", Each)
    Run("faces", Faces)
    Run("faces", FacesControl)
    Run("super", Super)
    Run("super", SuperControl)
