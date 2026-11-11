pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Compute(P:pair(a,b) where a:type,b:type):int=if(D:=dup[P])then D.C else 0
Values(P:pair(a,b) where a:type,b:type):[]int=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):V
Use(P:pair(a,b) where a:type,b:type)<suspends>:int=
    var Total:int=1
    defer:Print("source {Total}")
    R:=race:
        block:block{Rows:=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):block{defer:Print("cast {Total}");Sleep(0.1);V+Total};var Sum:int=0;for(V:Rows):set Sum+=V;Sum}
        block:
            defer:Print("other {Total}")
            set Total=10
            Sleep(0.3)
            -1
    R
Main()<suspends>:void=Print("result {Use(dup(int){})}")
