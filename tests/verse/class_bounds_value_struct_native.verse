# Comparable facts from a selected class case remain local to that case (#209).
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
wrap(t:type) := struct { V:t }
root(z:type) := class:
    A:z
tight(z:subtype(comparable)) := class(root(z)) {}
Native(P:root(wrap(t)),V:t where t:type):int =
    if (D:=tight[P]):
        if (NeedCmp[V,V],NeedCmp[D.A,D.A]) then 1 else 2
    else -1
Main():void = Print("{Native(tight(wrap(int)){A:=wrap(int){V:=1}},1)}")
