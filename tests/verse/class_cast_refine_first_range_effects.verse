# First tries later elements without evaluating either bound again. Failed
# casts and empty ranges undo bound writes; a failed lower skips the upper.
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
Direct(H:cell,P:pair(a,b),Q:pair(c,d),Stop:logic where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,int,string)=
    first{I:=Mark(H,"L")+dup[P].Lo..Upper(H,Stop)+dup[Q].Hi;I>1;(I,H.N,H.Trace)}
Named(H:cell,P:pair(a,b),Q:pair(c,d),Stop:logic where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,int,string)=
    first{L:=Mark(H,"L");D:=dup[P];U:=Upper(H,Stop);E:=dup[Q];I:=L+D.Lo..U+E.Hi;I>1;(I,H.N,H.Trace)}
Main()<transacts>:void=
    H:=cell{}
    K:=cell{}
    Y:pair(int,int)=dup(int){}
    Z:pair(int,int)=pair(int,int){}
    if(V:=Direct[H,Y,Y,false]) then Print("direct {V(0)} {V(1)} {V(2)}") else Print("wrong")
    if(V:=Named[K,Y,Y,false]) then Print("named {V(0)} {V(1)} {V(2)}") else Print("wrong")
    Print("after {H.N} '{H.Trace}' / {K.N} '{K.Trace}'")
    if(V:=Direct[H,Z,Y,true]) then Print("wrong") else Print("lower {H.N} '{H.Trace}'")
    if(V:=Named[K,Z,Y,true]) then Print("wrong") else Print("lower named {K.N} '{K.Trace}'")
    if(V:=Direct[H,Y,Z,false]) then Print("wrong") else Print("upper {H.N} '{H.Trace}'")
    if(V:=Named[K,Y,Z,false]) then Print("wrong") else Print("upper named {K.N} '{K.Trace}'")
    Empty:=dup(int){Lo:=3}
    if(V:=Direct[H,Empty,Y,false]) then Print("wrong") else Print("empty {H.N} '{H.Trace}'")
    if(V:=Named[K,Empty,Y,false]) then Print("wrong") else Print("empty named {K.N} '{K.Trace}'")
