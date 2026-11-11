# Comparable facts from a selected class case remain local to that case (#209).
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := interface:
    A:t
    Hit(N:t):int
tight(t:subtype(comparable),u:subtype(comparable)) := class(root(t)):
    E:u
    Hit<override>(N:t):int = if (A=N,E=E) then 1 else 2
Native(P:root(t) where t:type):int =
    if (D:=tight[P]):
        if (NeedCmp[P.A,P.A],NeedCmp[D.E,D.E]) then P.Hit(P.A) else 0
    else -1
Run(P:root(t) where t:type):int = P.Hit(P.A)
Main():void =
    P:=tight(int,string){A:=3,E:="s"}
    Print("{Native(P)} {Run(P)}")
