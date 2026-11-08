# code generic over a hierarchy whose concrete classes all fix the type
# argument: receivers read from fields, arrays, for loops and if-bindings,
# and variables of its type, start as a hidden placeholder object (#157)
expr(t:type) := class<abstract>:
    Eval():t
int_lit := class(expr(int)):
    N:int
    Eval<override>():int = N
neg := class(expr(int)):
    E:expr(int)
    Eval<override>():int = -E.Eval()
bool_lit := class(expr(logic)):
    B:logic
    Eval<override>():logic = B
holder(t:type) := class:
    E:expr(t)
All(Es:[]expr(t) where t:type):[]t = for (E : Es) { E.Eval() }
First(Es:[]expr(t), X:t where t:type):t = if (E := Es[0]) then E.Eval() else X
Held(H:holder(t) where t:type):t = H.E.Eval()
Last(Es:[]expr(t), X:t where t:type):t =
    var Cur:?expr(t) = false
    for (E : Es) { set Cur = option{E} }
    if (C := Cur?) then C.Eval() else X
src(t:type) := interface:
    Next():t
ints := class(src(int)):
    N:int
    Next<override>():int = N + 1
Pull(Ss:[]src(t), X:t where t:type):t =
    var R:t = X
    for (S : Ss) { set R = S.Next() }
    R
Main():void =
    for (X : All(array{int_lit{N := 3}, neg{E := int_lit{N := 4}}})) { Print("{X}") }
    Print("{First(array{int_lit{N := 3}}, 0)}")
    Print("{Held(holder(int){E := neg{E := int_lit{N := 9}}})}")
    if (Held(holder(logic){E := bool_lit{B := true}})?) then Print("true")
    Print("{Last(array{int_lit{N := 1}, int_lit{N := 2}}, 0)}")
    Print("{Last(array{}, 7)}")
    Print("{Pull(array{ints{N := 5}, ints{N := 6}}, 0)}")
