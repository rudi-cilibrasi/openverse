root(t:type) := interface:
    Picks():int = 1 | 2
wide(t:type,u:type) := class(root(t)):
    Picks<override>():int =
        E:[]u = Concatenate()
        E.Length + 10 | E.Length + 20
plain(t:type,u:type) := class(wide(t,u)) {}
Get(X:root(t) where t:type):[]int = for (V := X.Picks()) { V }
Main():void =
    for (V : Get(plain(int,string){})) { Print("{V}") }
    for (V : Get(plain(string,int){})) { Print("{V}") }
