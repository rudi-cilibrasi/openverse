pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Index:int=0}
Echo(X:t,?Other:t=X where t:type):t=Other
cell:=class{var Trace:string=""}
dog:=class<unique>{}
Key(H:cell,N:int)<transacts>:?int={set H.Trace+="K";option{N}}
Value(H:cell,X:t where t:type)<transacts>:t={set H.Trace+="V";X}
Build(P:pair(a,b),H:cell where a:type,b:type)<decides>:[?int]b=
    map{Key(H,0)=>Echo(P.A,?Other:=Value(H,dup[P].B)),Key(H,1)=>Echo(P.A,?Other:=Value(H,dup[P].A))}
Named(P:pair(a,b),H:cell where a:type,b:type)<decides>:[?int]b=
    K:=Key(H,0)
    D:=dup[P]
    V:=Value(H,D.B)
    L:=Key(H,1)
    W:=Value(H,D.A)
    map{K=>V,L=>W}
EmptyKey(P:pair(a,b) where a:type,b:type)<decides>:[?int]b=
    map{false=>Echo(P.A,?Other:=dup[P].B)}
KnownKey(P:pair(a,b),K:dog where a:type,b:type)<decides>:[dog]b=
    map{K=>Echo(P.A,?Other:=dup[P].B)}
animal:=class<abstract>{}
cat:=class(animal){N:int=1}
Empty(?Default:?t=false where t:type):?t=Default
Choose(X:t,Y:t,Values:[?int]int where t:type):t=Y
Unrelated(P:pair(a,b),A:animal where a:type,b:type)<decides>:b=
    Choose(P.A,dup[P].B,map{Empty()=>cat[A].N})
Repeated(P:pair(a,b) where a:type,b:type)<decides>:b=
    Choose(P.A,dup[P].B,map{Empty()=>dup[P].Index})
Main():void=
    H:=cell{}
    P:=dup(int){A:=7,B:=9}
    if(M:=Build[P,H],A:=M[option{0}],B:=M[option{1}])then Print("map {A} {B} {H.Trace}")else Print("wrong")
    J:=cell{}
    if(M:=Named[P,J],A:=M[option{0}],B:=M[option{1}])then Print("named {A} {B} {J.Trace}")else Print("wrong")
    if(M:=Build[pair(int,string){A:=7,B:="other"},H])then Print("wrong")else Print("rollback {H.Trace}")
    if(M:=EmptyKey[dup(string){A:="left",B:="right"}],V:=M[false])then Print("empty {V}")else Print("wrong")
    D:=dog{}
    if(M:=KnownKey[P,D],V:=M[D])then Print("object {V}")else Print("wrong")
    if(V:=Unrelated[P,cat{}],W:=Repeated[P])then Print("context {V} {W}")else Print("wrong")
    for(M:=map{(1|2)=>3}){Print("choice {M.Length}")}
    for(M:=map{1+(1|2)=>3}){Print("nested choice {M.Length}")}
