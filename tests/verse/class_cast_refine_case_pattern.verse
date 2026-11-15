# Computed patterns are separate failure conditions: failed casts and
# mismatches undo their writes, later patterns run in order, and a match
# skips all later patterns. The named control gives the cast its own option.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class:
    var N:int=0
Mark(H:cell,Delta:int,Value:int)<transacts>:int=
    set H.N+=Delta
    Value
Direct(H:cell,P:pair(a,b),N:int where a:type,b:type)<transacts>:int=
    case(N):
        Mark(H,1,0)+dup[P].C => 10
        Mark(H,10,0) => 20
        _ => 30
Named(H:cell,P:pair(a,b),N:int where a:type,b:type)<transacts>:int=
    case(N):
        option{M:=Mark(H,1,0);D:=dup[P];M+D.C}? => 10
        Mark(H,10,0) => 20
        _ => 30
Main()<transacts>:void=
    H:=cell{}
    K:=cell{}
    Ps:[]pair(int,int)=array{dup(int){},pair(int,int){}}
    for(P:Ps,N:array{4,0,9}):
        Print("direct {N} {Direct(H,P,N)} count {H.N}")
        Print("named {N} {Named(K,P,N)} count {K.N}")
