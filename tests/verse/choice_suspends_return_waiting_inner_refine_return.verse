pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }

Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    for(A:=(4|5),B:=(4|5)):
        if(F:=dup[P]):
            set Total=7
            Sleep(0.01)
            return Total
    -1
Main()<suspends>:void = Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})}")
