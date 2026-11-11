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
    for(U:=if(F:=dup[P])then(F.C|F.C+1)else 0):
        if(V:=Left[C,2],W:=if(D:=dup[P])then block{set Total+=V;D.C|D.C+1}else 0,Z:=if(E:=dup[Q])then block{set Total+=W;E.C|E.C+1}else 0,V=1,W=5,Z=5):
            Print("win {V} {W} {Z} {Total} {C.N}")
        if(V:=Left[C,2],W:=if(D:=dup[P])then block{set Total+=V;D.C|D.C+1}else 0,Z:=if(E:=dup[Q])then block{set Total+=W;E.C|E.C+1}else 0,V=99,W=5,Z=5)then Print("bad")else Print("none {Total} {C.N}")
    Sleep(0.5)
Main()<suspends>:void = Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
