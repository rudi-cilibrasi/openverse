# Independent casts in one bound retain both equalities in aggregate results.
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Lo:int=1;Hi:int=2}
Add(X:int,Y:int)<transacts>:int=X+Y
Lower(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts>:[]tuple(int,b,d)=
    for(I:=Add(dup[P].Lo,dup[Q].Lo)..2){(I,P.A,Q.A)}
Upper(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts>:[]tuple(int,b,d)=
    for(I:=2..Add(dup[P].Hi,dup[Q].Hi)){(I,P.A,Q.A)}
Both(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts>:[]tuple(tuple(b,d),int)=
    for(I:=Add(Add(dup[P].Lo,dup[Q].Lo),0)..Add(dup[P].Hi,dup[Q].Hi)){((P.A,Q.A),I)}
First(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,b,d)=
    first{I:=Add(dup[P].Lo,dup[Q].Lo)..Add(dup[P].Hi,dup[Q].Hi);I>2;(I,P.A,Q.A)}
Named(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts>:[]tuple(int,b,d)=
    if(D:=dup[P],E:=dup[Q])then for(I:=Add(D.Lo,E.Lo)..2){(I,P.A,Q.A)}else array{}
Values(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts>:[]tuple(b,d)=
    for(I:=Add(dup[P].Lo,dup[Q].Lo)..2){(P.A,Q.A)}
Shared(P:pair(a,b),Q:pair(c,d),X:a,Y:c where a:type,b:type,c:type,d:type)<transacts>:[]tuple(b,d)=
    for(I:=Add(dup[P].Lo,dup[Q].Lo)..2){(X,Y)}
Triple(P:pair(a,b),Q:pair(c,d),R:pair(e,f) where a:type,b:type,c:type,d:type,e:type,f:type)<transacts>:[]tuple(b,d,f)=
    for(I:=Add(Add(dup[P].Lo,dup[Q].Lo),dup[R].Lo)..3){(P.A,Q.A,R.A)}
Main():void=
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    for(V:Lower(P,Q)){Print("lower {V(0)} {V(1)} {V(2)}")}
    for(V:Values(P,Q)){Print("values {V(0)} {V(1)}")}
    for(V:Named(P,Q)){Print("named {V(0)} {V(1)} {V(2)}")}
    for(V:Upper(P,Q)){Print("upper {V(0)} {V(1)} {V(2)}")}
    for(V:Both(P,Q)){Print("both {V(1)} {V(0)(0)} {V(0)(1)}")}
    if(V:=First[P,Q])then Print("first {V(0)} {V(1)} {V(2)}")else Print("wrong")
    for(V:Shared(P,Q,11,"shared")){Print("shared {V(0)} {V(1)}")}
    for(V:Triple(P,Q,dup(int){A:=13,B:=15})){Print("triple {V(0)} {V(1)} {V(2)}")}
    Bad:=pair(int,string){A:=1,B:="other"}
    Print("missing {Lower(Bad,Q).Length} {Lower(P,Bad).Length} {Upper(Bad,Q).Length} {Upper(P,Bad).Length}")
    if(V:=First[P,Bad])then Print("wrong")else Print("first missing")
