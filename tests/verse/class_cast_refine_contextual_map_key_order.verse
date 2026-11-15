pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Echo(X:t,?Other:t=X where t:type):t=Other
cell:=class{var Trace:string=""}
DefaultCount(H:cell)<transacts>:int={set H.Trace+="d";0}
Key(H:cell,S:string,?Count:int=DefaultCount(H),?Default:?t=false where t:type)<transacts>:?t={set H.Trace+=S;Default}
Object(H:cell,S:string,P:pair(a,b) where a:type,b:type)<transacts>:pair(a,b)={set H.Trace+=S;P}
Value(H:cell,S:string,X:t where t:type)<transacts>:t={set H.Trace+=S;X}
Build(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<decides>:[?int]tuple(b,d)=
    map{Key(H,"K")=>(Value(H,"P",Echo(P.A,?Other:=dup[Object(H,"A",P)].B)),Value(H,"Q",Echo(Q.A,?Other:=dup[Object(H,"B",Q)].B))),Key(H,"L",?Default:=option{0})=>(Value(H,"U",Echo(P.A,?Other:=dup[Object(H,"C",P)].A)),Value(H,"V",Echo(Q.A,?Other:=dup[Object(H,"D",Q)].A)))}
Main():void=
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    H:=cell{}
    if(M:=Build[P,Q,H],A:=M[false],B:=M[option{0}])then Print("{A(0)} {A(1)} {B(0)} {B(1)} {H.Trace}")else Print("wrong")
    J:=cell{}
    if(M:=Build[P,pair(int,string){A:=1,B:="bad"},J])then Print("wrong")else Print("rollback {J.Trace}")
    if(M:=Build[P,Q,J],false?)then Print("wrong")else Print("outer {J.Trace}")
