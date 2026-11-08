# choice inside expressions (#208), review cases: a call's or an index's
# head, a receiver and a field are read before the choice; set op= reads its
# old value first; operands before a choice keep their expected types
negative_percent := type{_X:float where -1.0 <= _X, _X <= 0.0}
Arr():[]int =
    Print("arr")
    array{10, 20}
c := class:
    V:int
    Get(X:int):int = V * 10 + X
store := class:
    var Items:[]int = array{10, 20}
    Clear():int =
        set Items = array{7, 8}
        0
counter := class:
    var N:int = 0
    Bump():int =
        set N = 100
        1
    Run():void =
        set N = 0
        if (set N += Bump() + (0 | 1)) then Print("op= old value first: {N}")
TakeOpt(O:?int, X:int):int = X
TakeArr(A:[]int, X:int):int = A.Length + X
Id(X:t where t:type):t = X
Apply(F:int->int, X:int):int = F(X)
Take(P:negative_percent, X:int):int = X
Main():void =
    for (V := Arr()[0 | 1]) { Print("head once {V}") }
    var A:[]int = array{10, 20}
    if (V := A[(set A = array{7, 8}; 0) | 1]) then Print("head first {V}")
    var O:c = c{V := 1}
    if (R := O.Get((set O = c{V := 2}; 0) | 1)) then Print("receiver first {R}")
    S := store{}
    if (V := S.Items[(S.Clear(); 0) | 1]) then Print("field first {V}")
    counter{}.Run()
    for (V := TakeOpt(false, 1 | 2)) { Print("false {V}") }
    for (V := TakeArr(array{}, 1 | 2)) { Print("array{} {V}") }
    for (V := Apply(Id, 1 | 2)) { Print("generic {V}") }
    for (V := Take(-0.5, 1 | 2)) { Print("refined {V}") }
