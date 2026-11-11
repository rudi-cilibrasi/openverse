box(t:type) := struct { E:[]t = Concatenate(); B:int }
root(t:type) := interface:
    Builds():box(t) = box{B:=1|2}
fixed := class(root(int)):
    Builds<override>():box(int) = box{B:=3|4}
extra(t:type,u:type) := class(root(t)):
    X:u
    Builds<override>():box(t) =
        E:[]u = Concatenate()
        box{B:=7|8}
Get(P:root(t) where t:type):[]box(t) = for (V:=P.Builds()) { V }
plain(t:type) := class(root(t)) {}
Main():void =
    for (V : Get(plain(string){})) { Print("p {V.E.Length} {V.B}") }
    for (V : Get(fixed{})) { Print("f {V.E.Length} {V.B}") }
    for (V : Get(extra(string,int){X:=1})) { Print("e {V.E.Length} {V.B}") }
