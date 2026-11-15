# Only the selected arm casts. A failed selected arm fails the whole case;
# it does not try the default, and its caller's preceding write rolls back.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class:
    var N:int=0
Direct(H:cell,P:pair(a,b),N:int where a:type,b:type)<transacts><decides>:int=
    set H.N+=1
    case(N):
        1 => dup[P].C
        _ => 0
Named(H:cell,P:pair(a,b),N:int where a:type,b:type)<transacts><decides>:int=
    set H.N+=1
    case(N):
        1 => (D:=dup[P];D.C)
        _ => 0
Main()<transacts>:void=
    H:=cell{}
    K:=cell{}
    Ps:[]pair(int,int)=array{dup(int){},pair(int,int){}}
    for(P:Ps,N:=0..1):
        if(V:=Direct[H,P,N]) then Print("direct {N} {V} count {H.N}") else Print("direct fail count {H.N}")
        if(V:=Named[K,P,N]) then Print("named {N} {V} count {K.N}") else Print("named fail count {K.N}")
