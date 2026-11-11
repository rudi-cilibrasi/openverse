# expect: must be comparable
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
tight(t:subtype(comparable)) := class(root(t)) {}
Reject(P:root(t) where t:type):void =
    V := if (D:=tight[P]) then D.A else P.A
    if (NeedCmp[V,V]) then Print("bad")
Main():void = Print("unused")
