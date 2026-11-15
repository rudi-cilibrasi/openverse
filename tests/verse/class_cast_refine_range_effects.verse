# Each bound runs once, lower before upper. A failed lower cast skips an
# upper operand that would Err; either failed cast rolls back bound writes.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)):
    Lo:int=1
    Hi:int=2
cell:=class:
    var N:int=0
    var Trace:string=""
Mark(H:cell,Tag:string)<transacts>:int=
    set H.N+=1
    set H.Trace+=Tag
    0
Upper(H:cell,Stop:logic)<transacts>:int=if(Stop?) then Err() else Mark(H,"U")
Direct(H:cell,P:pair(a,b),Q:pair(c,d),Stop:logic where a:type,b:type,c:type,d:type)<transacts>:[]tuple(int,int,string)=
    for(I:=Mark(H,"L")+dup[P].Lo..Upper(H,Stop)+dup[Q].Hi){(I,H.N,H.Trace)}
Named(H:cell,P:pair(a,b),Q:pair(c,d),Stop:logic where a:type,b:type,c:type,d:type)<transacts>:[]tuple(int,int,string)=
    for(L:=Mark(H,"L"),D:=dup[P],U:=Upper(H,Stop),E:=dup[Q],I:=L+D.Lo..U+E.Hi){(I,H.N,H.Trace)}
Main()<transacts>:void=
    H:=cell{}
    K:=cell{}
    Y:pair(int,int)=dup(int){}
    Z:pair(int,int)=pair(int,int){}
    for(V:Direct(H,Y,Y,false)){Print("direct {V(0)} {V(1)} {V(2)}")}
    for(V:Named(K,Y,Y,false)){Print("named {V(0)} {V(1)} {V(2)}")}
    Print("after {H.N} '{H.Trace}' / {K.N} '{K.Trace}'")
    Print("bad lower {Direct(H,Z,Y,true).Length} {Named(K,Z,Y,true).Length} {H.N} '{H.Trace}' / {K.N} '{K.Trace}'")
    Print("bad upper {Direct(H,Y,Z,false).Length} {Named(K,Y,Z,false).Length} {H.N} '{H.Trace}' / {K.N} '{K.Trace}'")
