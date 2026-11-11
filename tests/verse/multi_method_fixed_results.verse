box(t:type) := class:
    A:t
    B:t
    Both():t = A | B
fixed := class(box(int)):
    Both<override>():int = 70 | 80
extra(t:type,u:type) := class(box(t)):
    X:u
    Both<override>():t =
        E:[]u = Concatenate()
        A | A
Count(P:box(t) where t:type):int =
    R := for (V := P.Both()) { V }
    R.Length
Main()<decides>:void =
    Is:[]box(int) = array{box(int){A:=1,B:=2},fixed{A:=3,B:=4},extra(int,string){A:=5,B:=6,X:="s"}}
    for (P : Is,V := P.Both()) { Print("int {V}") }
    Print("count {Count(fixed{A:=3,B:=4})} {Count(extra(string,int){A:="a",B:="b",X:=1})}")
