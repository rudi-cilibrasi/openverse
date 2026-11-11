pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
counter := class { var N:int=0 }
Left(C:counter,N:int)<transacts><decides>:int =
    N>=0
    set C.N+=1
    N|Right[C,N-1]
Right(C:counter,N:int)<transacts><decides>:int =
    N>=0
    set C.N+=1
    N|Left[C,N-1]
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    C:=counter{}
    var Total:int=0
    branch:
        Sleep(0.25)
        Print("observe {Total}")
    for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        if(V:=Left[C,1],W:=if(F:=dup[P])then block{set Total+=V+1;F.C|F.C+1}else 0,V=0,W=5):
            set Total+=A+B
            Print("row {A} {B} {Total} {C.N}")
    Print("source {Total}")
    Sleep(0.5)
Main()<suspends>:void = Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
