# Comparable facts from a selected class case remain local to that case (#209).
root(t:type) := class:
    A:t
    Both(?Q:[]t=Concatenate()):t = A
tight(t:subtype(comparable),u:subtype(comparable)) := class(root(t)):
    E:u
    Both<override>(?Q:[]t=block{V:[]t=Concatenate(); W:[]u=Concatenate(); if (V=V,W=W) then V else V}):t =
        if (E=E) then (A) else A
Get(P:root(t) where t:type):[]t = for(V:=P.Both()) { V }
Main():void =
    for(V:Get(tight(int,string){A:=7,E:="s"})) { Print("{V}") }
    for(V:Get(tight(string,int){A:="s",E:=7})) { Print(V) }
