# GADT evaluation (#243): each branch typed under what its cast tells of t
expr(t:type) := class<abstract>:
    Tag():string
lit := class(expr(int)):
    V:int
    Tag<override>():string = "lit"
boolE := class(expr(logic)):
    V:logic
    Tag<override>():string = "bool"
add := class(expr(int)):
    L:expr(int)
    R:expr(int)
    Tag<override>():string = "add"
cond(t:type) := class(expr(t)):
    C:expr(logic)
    Then:expr(t)
    Else:expr(t)
    Tag<override>():string = "cond"
Eval(E:expr(t) where t:type):t =
    if (L := lit[E]) then L.V
    else if (B := boolE[E]) then B.V
    else if (A := add[E]) then Eval(A.L) + Eval(A.R)
    else if (C := cond[E]) then (if (Eval(C.C)?) then Eval(C.Then) else Eval(C.Else))
    else Err()
Main():void =
    E:expr(int) = cond(int){C := boolE{V := true}, Then := add{L := lit{V := 2}, R := lit{V := 3}}, Else := lit{V := 0}}
    Print("{Eval(E)}")
    F:expr(logic) = cond(logic){C := boolE{V := false}, Then := boolE{V := true}, Else := boolE{V := false}}
    Print("{if (Eval(F)?) then "yes" else "no"}")
