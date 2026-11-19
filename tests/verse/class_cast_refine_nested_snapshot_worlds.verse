expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){var Lo:int=1;Hi:int=2}
cell:=class{var Trace:string=""}
Read(H:cell,S:string,N:int)<transacts>:int={set H.Trace+=S;N}
Change(H:cell,P:dup(int),Q:pair(c,d) where c:type,d:type)<transacts>:pair(c,d)={set H.Trace+="C";set P.Lo=5;Q}
Add(X:int,Y:int)<transacts>:int=X+Y
F(P:pair(a,b),Q:pair(c,d),H:cell,R:dup(int) where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,b,d)=first{I:=Add(Read(H,"L",dup[P].Lo),Read(H,"R",dup[Change(H,R,Q)].Lo))..2;(I,P.A,Q.A)}
Nested(E:expr(t),P:pair(a,b),Q:pair(c,d),H:cell,Owner:dup(int) where t:type,a:type,b:type,c:type,d:type)<transacts>:?tuple(t,int,b,d)=
    if(Print("outer"),VP:=vpair[E],Saved:=VP.L,LL:=lit[Saved],set VP.L=lit{V:=99},LR:=lit[VP.R])then block:
        if(V:=F[P,Q,H,Owner])then option{((LL.V,LR.V),V(0),V(1),V(2))}else false
    else false
Decide(E:expr(t),P:pair(a,b),Q:pair(c,d),H:cell,Owner:dup(int) where t:type,a:type,b:type,c:type,d:type)<transacts><decides>:?t=
    if(Print("outer"),VP:=vpair[E],Saved:=VP.L,LL:=lit[Saved],set VP.L=lit{V:=99},LR:=lit[VP.R])then block:
        V:=F[P,Q,H,Owner]
        option{(LL.V,LR.V)}
    else false
Main():void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=4}}
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    H:=cell{}
    Result:=Nested(E,P,Q,H,P)
    if(V:=Result?)then Print("nested {V(0)(0)} {V(0)(1)} {V(1)} {V(2)} {V(3)}")else Print("wrong")
    Print("{H.Trace} {P.Lo} {E.L.Eval()}")
    Bad:=pair(string,string){A:="bad",B:="bad"}
    E2:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=4}}
    P2:=dup(int){A:=7,B:=9}
    H2:=cell{}
    NoValue:=Nested(E2,P2,Bad,H2,P2)
    if(V:=NoValue?)then Print("wrong")else Print("none {E2.L.Eval()} {H2.Trace} {P2.Lo}")
    E3:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=4}}
    P3:=dup(int){A:=7,B:=9}
    H3:=cell{}
    if(V:=Decide[E3,P3,Bad,H3,P3])then Print("wrong normal")else Print("failed {E3.L.Eval()} {H3.Trace} {P3.Lo}")
