pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int =
    var Pass:int=0
    defer:Print("source {Pass}")
    loop:
        defer:Print("loop {Pass}")
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
            if(Pass=1)then return A+B
        set Pass+=1
        if(Pass>1)then break
    -1
Main()<suspends>:void = Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})}")
