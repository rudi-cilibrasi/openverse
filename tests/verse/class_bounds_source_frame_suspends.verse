# Comparable facts from a selected class case remain local to that case (#209).
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
tight(t:subtype(comparable)) := class(root(t)) {}
Run(P:root(t) where t:type)<suspends>:void =
    var V:t = P.A
    if (D:=tight[P]):
        Sleep(0.01)
        set V = D.A
        if (NeedCmp[V,P.A]) then Print("same")
Main()<suspends>:void =
    Run(tight(int){A:=3})
    Run(root(string){A:="s"})
