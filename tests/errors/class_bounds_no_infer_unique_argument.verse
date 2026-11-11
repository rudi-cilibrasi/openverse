# expect: must be comparable
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
holder(t:type) := class<unique>:
    V:t
root(z:type) := class:
    A:z
tight(z:subtype(comparable)) := class(root(z)) {}
Reject(P:root(holder(t)),V:t where t:type):void =
    if (D:=tight[P]):
        if (NeedCmp[V,V]) then Print("bad")
Main():void = Print("unused")
