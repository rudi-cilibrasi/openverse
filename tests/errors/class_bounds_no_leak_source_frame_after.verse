# expect: must be comparable
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
tight(t:subtype(comparable)) := class(root(t)) {}
Reject(P:root(t) where t:type)<suspends>:void =
    var V:t = P.A
    if (D:=tight[P]):
        Sleep(0.01)
        set V = D.A
        if (NeedCmp[V,P.A]) then Print("same")
    if (NeedCmp[V,V]) then Print("bad")
Main():void = Print("unused")
