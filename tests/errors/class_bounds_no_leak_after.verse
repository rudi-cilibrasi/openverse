# expect: must be comparable
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
    Hit(N:t):int = 0
tight(t:subtype(comparable)) := class(root(t)):
    Hit<override>(N:t):int = if (A=N) then 1 else 2
Reject(P:root(t) where t:type)<decides>:void =
    if (D:=tight[P]) then Print("selected") else Print("else")
    NeedCmp[P.A,P.A]
Main():void = Print("unused")
