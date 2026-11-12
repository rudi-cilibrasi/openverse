# A cast that refines type arguments in option{…}, logic{…}, not, and, or
# and first{…} (#243): the clauses after it, in the braces or the operand,
# are its branch, typed under the refinement; their failure, or the cast's,
# is the failure context's, which undoes what it did. The names they bind
# end with it.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
cell := class:
    var N:int = 0
# the value of option{…} at a type that holds under the refinement only
Opt(P:pair(a, b) where a:type, b:type):?a = option{D := dup[P]; D.B}
# without a type there: the branch's own, int
OptC(P:pair(a, b) where a:type, b:type):int =
    X := option{D := dup[P]; D.C * 2}
    if (V := X?) then V else -1
# effects before and after, undone with the failure
Undo(H:cell, P:pair(a, b), Min:int where a:type, b:type)<transacts>:?int =
    option{set H.N += 1; Print("in"); D := dup[P]; set H.N += D.C; D.C > Min; H.N}
Logic(P:pair(a, b) where a:type, b:type):logic = logic{dup[P]}
Not(P:pair(a, b) where a:type, b:type):int = if (not dup[P]) then 1 else 0
And(P:pair(a, b), N:int where a:type, b:type):int = if (N > 0 and (D := dup[P]; D.C > N)) then 1 else 0
Or(P:pair(a, b), N:int where a:type, b:type):int = if ((D := dup[P]; D.C > N) or N < 0) then 1 else 0
# first{…} with a choice before the cast and after it
FirstBefore(P:pair(a, b) where a:type, b:type):int =
    if (V := first{X := (1 | 2 | 3); X > 1; D := dup[P]; D.C + X}) then V else -1
FirstAfter(P:pair(a, b) where a:type, b:type):int =
    if (V := first{D := dup[P]; X := (D.C | D.C + 1); X > 4; X}) then V else -1
Main()<transacts>:void =
    H := cell{}
    Y:pair(int, int) = dup(int){A := 1, B := 2}
    Z:pair(int, string) = pair(int, string){A := 1, B := "s"}
    if (V := Opt(Y)?) then Print("Opt {V}")
    if (V := Opt(Z)?) then Print("Opt {V}") else Print("Opt no")
    Print("OptC {OptC(Y)} {OptC(Z)}")
    if (V := Undo(H, Y, 3)?) then Print("Undo {V}")
    if (V := Undo(H, Y, 9)?) then Print("Undo {V}") else Print("Undo no {H.N}")
    if (V := Undo(H, Z, 0)?) then Print("Undo {V}") else Print("Undo no {H.N}")
    if (Logic(Y)?, not Logic(Z)?) then Print("Logic")
    Print("Not {Not(Y)} {Not(Z)}")
    Print("And {And(Y, 3)} {And(Y, 4)} {And(Z, 1)}")
    Print("Or {Or(Y, 3)} {Or(Y, 4)} {Or(Z, -1)} {Or(Z, 1)}")
    Print("First {FirstBefore(Y)} {FirstBefore(Z)} {FirstAfter(Y)} {FirstAfter(Z)}")
