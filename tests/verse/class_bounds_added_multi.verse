# Comparable facts from a selected class case remain local to that case (#209).
root(t:type) := class:
    A:t
    Both():t = A | A
extra(t:subtype(comparable),u:subtype(comparable)) := class(root(t)):
    E:u
    Both<override>():t = if (E=E) then (A | A) else A
Get(P:root(t) where t:type):[]t = for(V:=P.Both()) { V }
Main():void =
    for(V:Get(extra(int,string){A:=7,E:="s"})): Print("{V}")
    for(V:Get(extra(string,int){A:="s",E:=7})): Print(V)
