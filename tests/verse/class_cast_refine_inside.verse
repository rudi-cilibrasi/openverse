# A cast that refines type arguments inside an expression of a failure
# context (#243): lifted out of it to be a clause of its own, as a choice
# there is, the operands evaluated before it bound first so they still run
# before it; the rest of the failure context is then its branch.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
    Same():t = B
cell := class:
    var N:int = 0
Bump(H:cell, K:int)<transacts><decides>:int =
    K > 0
    set H.N += K
    K
Show(X:int):string = "<{X}>"
Id(X:t where t:type):t = X
# a member of a cast in an if's condition
Cond(P:pair(a, b) where a:type, b:type):int =
    if (dup[P].C > 3) then 1 else 0
# a cast in an argument, after an operand with effects, in a <decides> body:
# the operand runs first, and is undone when the cast fails
Arg(H:cell, P:pair(a, b) where a:type, b:type)<transacts><decides>:string =
    Bump[H, 1] + dup[P].C > 0
    Show(dup[P].C)
# a method of the cast, its value at b; the cast as a whole argument
Val(P:pair(a, b) where a:type, b:type)<decides>:b = dup[P].Same()
Whole(P:pair(a, b) where a:type, b:type)<decides>:b = Id(dup[P]).A
# in option{} and a for's clause
Opt(P:pair(a, b) where a:type, b:type):?int = option{dup[P].C * 10}
Fil(Ps:[]pair(a, b) where a:type, b:type):[]int = for (P : Ps, dup[P].C > 3) { 1 }
# in a branch of an if, the cast written as a clause of a block there
Br(P:pair(a, b), N:int where a:type, b:type):?int = option{X := (if (N > 0) then (D := dup[P]; D.C) else 0); X + 1}
Main()<transacts>:void =
    H := cell{}
    Y:pair(int, int) = dup(int){A := 1, B := 2}
    Z:pair(int, int) = pair(int, int){A := 1, B := 2}
    Print("Cond {Cond(Y)} {Cond(Z)}")
    if (V := Arg[H, Y]) then Print("Arg {V} {H.N}")
    if (V := Arg[H, Z]) then Print("Arg {V}") else Print("Arg no {H.N}")
    if (V := Val[Y]) then Print("Val {V}")
    if (V := Whole[Y]) then Print("Whole {V}")
    if (V := Opt(Y)?) then Print("Opt {V}")
    if (V := Opt(Z)?) then Print("Opt {V}") else Print("Opt no")
    Print("Fil {Fil(array{Y, Z, Y}).Length}")
    for (P : array{Y, Z}, N : array{0, 1}):
        if (V := Br(P, N)?) then Print("Br {N} {V}") else Print("Br {N} no")
