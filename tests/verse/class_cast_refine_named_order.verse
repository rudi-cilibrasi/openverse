pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
cell:=class{var Trace:string=""}
Mark(H:cell,S:string)<transacts>:int=
    set H.Trace+=S
    0
Pick(H:cell,N:int,?X:int=0,?Y:int=0,?Z:int=Mark(H,"D"))<transacts>:int=
    set H.Trace+="C"
    N+X+Y+Z
Direct(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(b,d)=
    N:=Pick(H,Mark(H,"P"),?Y:=Mark(H,"Y")+dup[Q].Index,?X:=Mark(H,"X")+dup[P].Index)
    (P.A,Q.A)
Named(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(b,d)=
    N:=Mark(H,"P")
    Y:=Mark(H,"Y")
    DQ:=dup[Q]
    X:=Mark(H,"X")
    DP:=dup[P]
    V:=Pick(H,N,?Y:=Y+DQ.Index,?X:=X+DP.Index)
    (P.A,Q.A)
Main():void=
    H:=cell{}
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    if(V:=Direct[P,Q,H])then Print("direct {V(0)} {V(1)} {H.Trace}")
    J:=cell{}
    if(V:=Named[P,Q,J])then Print("named {V(0)} {V(1)} {J.Trace}")
    if(V:=Direct[P,pair(int,string){A:=1,B:="no"},H])then Print("wrong")else Print("rollback {H.Trace}")
    if(V:=Direct[pair(int,string){A:=1,B:="no"},Q,H])then Print("wrong")else Print("rollback late {H.Trace}")
