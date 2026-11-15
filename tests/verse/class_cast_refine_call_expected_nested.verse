pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Index:int=0}
Echo(X:t,?Other:t=X where t:type):t=Other
Wrap(X:t where t:type):t=X
Outer(X:t,Y:u,?Other:u=Y where t:type,u:type):t=X
box(t:type):=struct{Value:t}
Deep(P:pair(a,b) where a:type,b:type)<decides>:b=Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Echo(P.A,?Other:=dup[P].B)))))))))))))))))))))))))
Context(P:pair(a,b) where a:type,b:type)<decides>:b=Outer(P.A,P.B,?Other:=Echo(P.A,?Other:=dup[P].B))
Construct(P:pair(a,b) where a:type,b:type)<decides>:box(b)=box(b){Value:=Outer(P.A,P.B,?Other:=Echo(P.A,?Other:=dup[P].B))}
Named(P:pair(a,b) where a:type,b:type)<decides>:b=
    D:=dup[P]
    Outer(P.A,P.B,?Other:=Echo(P.A,?Other:=D.B))
Sequence(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<decides>:tuple(b,d)=
    V:b=Echo(P.A,?Other:=dup[P].B)
    W:d=Echo(Q.A,?Other:=dup[Q].B)
    (V,W)
Main():void=
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    if(A:=Deep[P],B:=Context[P],C:=Construct[P],D:=Named[P])then Print("int {A} {B} {C.Value} {D}")else Print("wrong")
    if(A:=Deep[Q],B:=Context[Q],C:=Construct[Q],D:=Named[Q])then Print("string {A} {B} {C.Value} {D}")else Print("wrong")
    if(V:=Sequence[P,Q])then Print("sequence {V(0)} {V(1)}")else Print("wrong")
    if(V:=Deep[pair(int,string){A:=7,B:="other"}])then Print("wrong")else Print("missing")
