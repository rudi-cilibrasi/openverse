# Comparable facts from a selected class case remain local to that case (#209).
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(a:type,b:type) := class:
    A:a
    B:b
same(t:subtype(comparable)) := class(root(t,t)) {}
Native(P:root(a,b) where a:type,b:type):int =
    if (D:=same[P]):
        if (NeedCmp[P.A,P.A], NeedCmp[P.B,P.B], NeedCmp[D.A,D.B]) then 1 else 2
    else -1
Main():void =
    Print("{Native(same(int){A:=3,B:=3})}")
    Print("{Native(root(int,string){A:=3,B:="s"})}")
