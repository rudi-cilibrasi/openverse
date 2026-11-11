# Comparable facts from a selected class case remain local to that case (#209).
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
    Hit(N:t):int = 0
tight(t:subtype(comparable)) := class(root(t)):
    Hit<override>(N:t):int = if (A=N) then 1 else 2
Native(P:root(t) where t:type):int =
    Vs:[]t = array{P.A}
    if (D:=tight[P]):
        if (NeedCmp[P.A,P.A], Vs=Vs) then D.Hit(P.A) else 0
    else -1
Main():void =
    Print("{Native(tight(int){A:=3})}")
    Print("{Native(root(string){A:="s"})}")
