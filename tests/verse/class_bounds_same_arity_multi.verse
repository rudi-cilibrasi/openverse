# Comparable facts from a selected class case remain local to that case (#209).
root(t:type) := class:
    A:t
    Both():t = A | A
tight(t:subtype(comparable)) := class(root(t)):
    Both<override>():t = if (A=A) then (A | A) else A
Get(P:root(t) where t:type):[]t = for(V:=P.Both()) { V }
Main():void =
    for(V:Get(tight(int){A:=7})) { Print("{V}") }
    for(V:Get(tight(string){A:="s"})) { Print(V) }
