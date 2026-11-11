pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Compute(P:pair(a,b) where a:type,b:type):int=if(D:=dup[P])then D.C else 0
Use(P:pair(a,b) where a:type,b:type)<suspends>:int=
    var Total:int=1
    defer:Print("source {Total}")
    R:=rush:
        block:
            defer:Print("cast {Total}")
            Sleep(0.1)
            if(D:=dup[P]):return D.C+Total
            0
        block:
            defer:Print("other {Total}")
            set Total=10
            Sleep(0.2)
            -1
    R
Main()<suspends>:void=
    Print("result {Use(dup(int){})}")
    Print("result {Use(pair(int,string){})}")
