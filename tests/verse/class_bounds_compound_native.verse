# Comparable facts from a selected class case remain local to that case (#209).
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(z:type) := class:
    A:z
tight(z:subtype(comparable)) := class(root(z)) {}
Native(P:root(tuple([]t,?t,[int]t)),V:t where t:type):int =
    if (D:=tight[P]):
        if (NeedCmp[V,V],NeedCmp[D.A,D.A]) then 1 else 2
    else -1
Main():void =
    P:=tight(tuple([]int,?int,[int]int)){A:=(array{1},option{1},map{1=>2})}
    Print("{Native(P,1)}")
