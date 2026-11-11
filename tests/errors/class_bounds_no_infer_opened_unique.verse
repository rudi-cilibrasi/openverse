# expect: must be comparable
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
holder(t:type) := class<unique>:
    V:t
root(z:subtype(comparable)) := class:
    A:z
wide(t:type) := class(root(holder(t))):
    E:t
Reject(P:root(z) where z:subtype(comparable)):void =
    if (D:=wide[P]):
        if (NeedCmp[D.E,D.E]) then Print("bad")
Main():void = Print("unused")
