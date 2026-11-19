pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){var Lo:int=1;Hi:int=2}
cell:=class{var Trace:string=""}
Read(H:cell,S:string,N:int)<transacts>:int={set H.Trace+=S;N}
Change(H:cell,P:dup(int),Q:pair(c,d) where c:type,d:type)<transacts>:pair(c,d)={set H.Trace+="C";set P.Lo=5;Q}
Add(X:int,Y:int)<transacts>:int=X+Y
F(P:pair(a,b),Q:pair(c,d),H:cell,R:dup(int) where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,b,d)=first{I:=Add(Read(H,"L",dup[P].Lo),Read(H,"R",dup[Change(H,R,Q)].Lo))..2;(I,P.A,Q.A)}
Choose(P:pair(a,b),Bad:pair(c,d),Good:pair(c,d),H:cell,R:dup(int) where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,b,d)=first{Q:=(Bad|Good);I:=Add(Read(H,"L",dup[P].Lo),Read(H,"R",dup[Change(H,R,Q)].Lo))..2;(I,P.A,Q.A)}
Main():void=
    P:=dup(int){A:=7,B:=9}
    Bad:=pair(string,string){A:="bad",B:="bad"}
    Good:=dup(string){A:="left",B:="right"}
    H:=cell{}
    if(V:=Choose[P,Bad,Good,H,P])then Print("choice {V(0)} {V(1)} {V(2)}")else Print("wrong")
    Print("{H.Trace} {P.Lo}")
    P2:=dup(int){A:=7,B:=9}
    H2:=cell{}
    if(V:=F[P2,Bad,H2,P2])then Print("wrong")else Print("rollback {H2.Trace} {P2.Lo}")
