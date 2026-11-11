# expect: must be comparable
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
tag(t:type) := struct { N:int }
root(z:type) := class:
    A:z
tight(t:subtype(comparable)) := class(root(tag(t))) {}
Reject(P:root(tag(t)),V:t where t:type):void =
    if (D:=tight[P]):
        if (NeedCmp[V,V]) then Print("bad")
Main():void = Print("unused")
