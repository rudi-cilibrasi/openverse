pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }

Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:Print("source {Total}")
    loop:
        defer:Print("loop {Total}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0,set Total+=1,if(B=4)then break else 0):
            return A+B
        Print("bad")
    99
Main()<suspends>:void = Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})}")
