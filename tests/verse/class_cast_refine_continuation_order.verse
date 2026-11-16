pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){var Lo:int=1;Hi:int=2}
cell:=class{var Trace:string=""}
Read(H:cell,S:string,N:int)<transacts>:int={set H.Trace+=S;N}
Change(H:cell,P:dup(int),Q:pair(c,d) where c:type,d:type)<transacts>:pair(c,d)={set H.Trace+="C";set P.Lo=5;Q}
Add(X:int,Y:int):int=X+Y
BodyValue(N:int)<computes><decides>:int=block{N>2;N}
BadValue(P:pair(a,b),Q:pair(c,d),H:cell,R:dup(int) where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,b,d)=first{I:=Add(Read(H,"L",dup[P].Lo),Read(H,"R",dup[Change(H,R,Q)].Lo))..3;(BodyValue[I],P.A,Q.A)}
Rows(P:pair(a,b),Q:pair(c,d),H:cell,R:dup(int) where a:type,b:type,c:type,d:type)<transacts>:[]tuple(int,int,b,d,int)=for(K:=0..1,I:=Add(Read(H,"L",dup[P].Lo),Read(H,"R",dup[Change(H,R,Q)].Lo))..3,J:=(0|1)){set R.Lo=2;(K,I,P.A,Q.A,J)}
Main():void=
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    H:=cell{}
    if(V:=BadValue[P,Q,H,P])then Print("value {V(0)} {H.Trace} {P.Lo}")else Print("wrong")
    P3:=dup(int){A:=7,B:=9}
    H2:=cell{}
    for(V:Rows(P3,Q,H2,P3)){Print("row {V(0)} {V(1)} {V(2)} {V(3)} {V(4)}")}
    Print("{H2.Trace} {P3.Lo}")
