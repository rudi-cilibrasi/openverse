# Comparing with an empty literal: the right operand takes the left's type
# (issue #7; the Core checker checks it against that type).
IsNone(O:?t where t:subtype(comparable))<decides>:void = O = false

Main():void =
    O:?int = false
    if (O = false) then Print("?int empty")
    P:?int = option{3}
    if (P <> false) then Print("?int full")
    E:[]int = array{}
    if (E = array{}) then Print("[]int empty")
    if (E = false) then Print("[]int false")
    M:[string]int = map{}
    if (M = map{}) then Print("map empty")
    if (IsNone[O], not IsNone[P]) then Print("generic too")
    S:string = ""
    if (S = "") then Print("string empty")
