# A scrutinee's cast refines its arms and following clauses. Its preceding
# operand runs once, before the cast, and rolls back when the cast fails.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class:
    var N:int=0
Mark(H:cell)<transacts>:int=
    set H.N+=10
    10
Keep(X:t,Y:t where t:type)<transacts>:t=Y
Direct(H:cell,P:pair(a,b) where a:type,b:type)<transacts><decides>:b=
    set H.N+=1
    X:b=case(Mark(H)+dup[P].C):
        14 => P.A
        _ => P.B
    set H.N+=100
    Keep(X,P.A)
Named(H:cell,P:pair(a,b) where a:type,b:type)<transacts><decides>:b=
    set H.N+=1
    M:=Mark(H)
    D:=dup[P]
    X:b=case(M+D.C):
        14 => P.A
        _ => P.B
    set H.N+=100
    Keep(X,P.A)
Main()<transacts>:void=
    H:=cell{}
    K:=cell{}
    if(V:=Direct[H,dup(int){A:=7,B:=9}]) then Print("direct {V} count {H.N}") else Print("direct fail count {H.N}")
    if(V:=Named[K,dup(int){A:=7,B:=9}]) then Print("named {V} count {K.N}") else Print("named fail count {K.N}")
    if(V:=Direct[H,pair(int,string){A:=1,B:="bad"}]) then Print("direct {V} count {H.N}") else Print("direct fail count {H.N}")
    if(V:=Named[K,pair(int,string){A:=1,B:="bad"}]) then Print("named {V} count {K.N}") else Print("named fail count {K.N}")
    if(V:=Direct[H,dup(string){A:="left",B:="right"}]) then Print("direct {V} count {H.N}") else Print("direct fail count {H.N}")
    if(V:=Named[K,dup(string){A:="left",B:="right"}]) then Print("named {V} count {K.N}") else Print("named fail count {K.N}")
