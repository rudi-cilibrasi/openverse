pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){}
Echo(X:t,?Other:t=X where t:type)<transacts>:t=Other
reader:=class:
    Copy(X:t,?Other:t=X where t:type)<transacts>:t=Other
Direct(P:pair(a,b) where a:type,b:type)<transacts><decides>:b=Echo(P.A,?Other:=dup[P].B)
Typed(P:pair(a,b) where a:type,b:type)<transacts><decides>:b=
    V:b=Echo(P.A,?Other:=dup[P].B)
    V
Method(P:pair(a,b) where a:type,b:type)<transacts><decides>:b=reader{}.Copy(P.A,?Other:=dup[P].B)
Named(P:pair(a,b) where a:type,b:type)<transacts><decides>:b=
    D:=dup[P]
    Echo(P.A,?Other:=D.B)
Tuple(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(b,d,b,d)=
    (P.A,Q.A,dup[P].B,dup[Q].B)
Main():void=
    P:=dup(int){A:=7,B:=9}
    if(A:=Direct[P],B:=Typed[P],C:=Method[P],D:=Named[P])then Print("int {A} {B} {C} {D}")else Print("wrong")
    Q:=dup(string){A:="left",B:="right"}
    if(A:=Direct[Q],B:=Typed[Q],C:=Method[Q],D:=Named[Q])then Print("string {A} {B} {C} {D}")else Print("wrong")
    if(V:=Direct[pair(int,string){A:=7,B:="other"}])then Print("wrong")else Print("missing")
    if(V:=Tuple[P,Q])then Print("tuple {V(0)} {V(1)} {V(2)} {V(3)}")else Print("wrong")
