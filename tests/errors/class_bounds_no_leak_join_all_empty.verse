# expect: must be comparable
None(V:t where t:type)<decides>:t =
    false?
    V
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
tight(t:subtype(comparable)) := class(root(t)) {}
Reject(P:root(t) where t:type):void =
    Vs := for (V := if (D:=tight[P]) then (D.A | D.A) else None[P.A]) { V }
    if (NeedCmp[Vs,Vs]) then Print("bad")
Main():void = Print("unused")
