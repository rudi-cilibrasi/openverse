# Indices precede receiver reads; the object reached then precedes RHS
# replacement, and += reads that object's old leaf after the RHS updates it.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){Index:int=0}
cell:=class{var V:int=0}
holder:=class{var Items:[]cell}
trace:=class{var Log:string=""}
ReadIndex(H:holder,Pick:cell,T:trace)<transacts>:int=
    set T.Log+="I"
    set H.Items=array{Pick}
    0
Rhs(H:holder,Pick:cell,Next:cell,T:trace,Stop:logic)<transacts>:int=
    if(Stop?)then Err()
    set T.Log+="R"
    set H.Items=array{Next}
    set Pick.V=10
    3
Direct(H:holder,Before:cell,Pick:cell,Next:cell,T:trace,P:pair(a,b),Stop:logic where a:type,b:type)<transacts><decides>:tuple(int,int,int,int,string)=
    R:=set H.Items[ReadIndex(H,Pick,T)+dup[P].Index].V+=Rhs(H,Pick,Next,T,Stop)
    (R,Before.V,Pick.V,H.Items[0].V,T.Log)
Named(H:holder,Before:cell,Pick:cell,Next:cell,T:trace,P:pair(a,b),Stop:logic where a:type,b:type)<transacts><decides>:tuple(int,int,int,int,string)=
    I:=ReadIndex(H,Pick,T)
    D:=dup[P]
    R:=set H.Items[I+D.Index].V+=Rhs(H,Pick,Next,T,Stop)
    (R,Before.V,Pick.V,H.Items[0].V,T.Log)
Main()<transacts>:void=
    B:=cell{V:=1}
    P:=cell{V:=2}
    N:=cell{V:=100}
    H:=holder{Items:=array{B}}
    T:=trace{}
    Alias:=P
    B2:=cell{V:=1}
    P2:=cell{V:=2}
    N2:=cell{V:=100}
    H2:=holder{Items:=array{B2}}
    T2:=trace{}
    Good:pair(int,int)=dup(int){}
    Bad:pair(int,int)=pair(int,int){}
    if(V:=Direct[H,B,P,N,T,Good,false])then Print("direct {V(0)} {V(1)} {V(2)} {V(3)} {V(4)} alias {Alias.V}")else Print("wrong")
    if(V:=Named[H2,B2,P2,N2,T2,Good,false])then Print("named {V(0)} {V(1)} {V(2)} {V(3)} {V(4)}")else Print("wrong")
    if(V:=Direct[H,B,P,N,T,Bad,true])then Print("wrong")else if(C:=H.Items[0])then Print("rollback {T.Log} {C.V} {Alias.V}")
    if(V:=Named[H2,B2,P2,N2,T2,Bad,true])then Print("wrong")else if(C:=H2.Items[0])then Print("rollback named {T2.Log} {C.V} {P2.V}")
