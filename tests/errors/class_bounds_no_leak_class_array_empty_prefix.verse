# expect: must be comparable
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
tight(t:subtype(comparable)) := class(root(t)) {}
Empty():[]int = array{}
Use(Cs:[]tight(t),V:t where t:subtype(comparable)):void =
    if (NeedCmp[V,V]) then Print("bad")
Reject(P:root(t) where t:type):void =
    Cs := for (I:Empty(), C := if (D:=tight[P]) then (D | D) else Err()) { C }
    Use(Cs,P.A)
Main():void = Print("unused")
