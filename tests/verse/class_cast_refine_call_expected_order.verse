pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){}
Echo(X:t,?Other:t=X where t:type):t=Other
cell:=class{var Trace:string=""}
Mark(H:cell,S:string,X:t where t:type)<transacts>:t=
    set H.Trace+=S
    X
Mix(H:cell,X:t,Y:u,?Left:t=X,?Right:u=Y,?Z:int=Mark(H,"D",0) where t:type,u:type)<transacts>:tuple(t,u)=
    set H.Trace+="C"
    (Left,Right)
Direct(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(b,d)=
    Mix(H,Mark(H,"P",P.A),Mark(H,"Q",Q.A),?Right:=Mark(H,"Y",dup[Q].B),?Left:=Mark(H,"X",dup[P].B))
Named(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(b,d)=
    A:=Mark(H,"P",P.A)
    B:=Mark(H,"Q",Q.A)
    DQ:=dup[Q]
    R:=Mark(H,"Y",DQ.B)
    DP:=dup[P]
    L:=Mark(H,"X",DP.B)
    Mix(H,A,B,?Right:=R,?Left:=L)
Stop(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(b,d)=
    V:tuple(b,d)=Mix(H,Mark(H,"P",P.A),Mark(H,"Q",Q.A),?Right:=Mark(H,"Y",dup[Q].B),?Left:=Mark(H,"X",dup[P].B))
    false?
    V
Main():void=
    H:=cell{}
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    if(V:=Direct[P,Q,H])then Print("direct {V(0)} {V(1)} {H.Trace}")else Print("wrong")
    J:=cell{}
    if(V:=Named[P,Q,J])then Print("named {V(0)} {V(1)} {J.Trace}")else Print("wrong")
    if(V:=Direct[P,pair(int,string){A:=7,B:="other"},H])then Print("wrong")else Print("early {H.Trace}")
    if(V:=Direct[pair(int,string){A:=7,B:="other"},Q,H])then Print("wrong")else Print("late {H.Trace}")
    if(V:=Stop[P,Q,H])then Print("wrong")else Print("after body {H.Trace}")
    if(V:=Direct[P,Q,H],false?)then Print("wrong")else Print("outer {H.Trace}")
