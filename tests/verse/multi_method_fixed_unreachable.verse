root(t:type) := interface:
    Picks():int
wide(u:type) := class(root(int)):
    Picks<override>():int =
        E:[]u = Concatenate()
        E.Length + 10 | E.Length + 20
plain(u:type) := class(wide(u)) {}
Get(P:root(t) where t:type):[]int = for (V:=P.Picks()) { V }
Main():void =
    for (V : Get(plain(string){})) { Print("{V}") }
    var Maybe:?root(string) = false
    if (P := Maybe?):
        for (V := P.Picks()) { Print("bad {V}") }
    Print("done")
