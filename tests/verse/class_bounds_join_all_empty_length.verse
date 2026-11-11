# Comparable facts from a selected class case remain local to that case (#209).
None(V:t where t:type)<decides>:t =
    false?
    V
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
tight(t:subtype(comparable)) := class(root(t)) {}
Run(P:root(t) where t:type):int =
    Vs := for (V := if (D:=tight[P]) then (D.A | D.A) else None[P.A]) { V }
    Vs.Length
Main():void =
    Print("{Run(tight(int){A:=3})}")
    Print("{Run(root(string){A:="s"})}")
