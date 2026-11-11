# Comparable facts from a selected class case remain local to that case (#209).
root(t:type) := class:
    A:t
    Hit(N:t):int = 0
tight(t:subtype(comparable)) := class(root(t)):
    Hit<override>(N:t):int = if (A=N) then 1 else 2
Run(P:root(t) where t:type):int = P.Hit(P.A)
Main():void =
    Print("{Run(tight(int){A:=3})}")
    Print("{Run(root(string){A:="s"})}")
