Two(N:int):int=N|N+1
Lazy(N:int)<computes><decides>:int=
    N>=0
    N|Lazy[N-1]
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){C:int=4}
Run(P0:pair(a0,b0),P1:pair(a1,b1),P2:pair(a2,b2),P3:pair(a3,b3),X:t where a0:type,b0:type,a1:type,b1:type,a2:type,b2:type,a3:type,b3:type,t:type):t=
    var Total:int=0
    defer:Print("source {Total}")
    if(A0:=if(D:=dup[P0])then(D.C|D.C+1)else 0,A1:=if(D:=dup[P1])then(D.C|D.C+1)else 0,A2:=if(D:=dup[P2])then(D.C|D.C+1)else 0,A3:=if(D:=dup[P3])then(D.C|D.C+1)else 0,set Total+=1,if(Total>0)then return X else 0):Print("normal")
    X
Main():void=Print("{Run(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},7)}")
