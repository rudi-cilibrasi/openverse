# The fields given run in the order written (#724), at the places the given
# fields have in declaration order. Prefix and inherited
# defaults run before the next cast, trailing defaults/blocks after it.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class:
    var N:int=0
    var Trace:string=""
Mark(H:cell,Tag:string,Value:int)<transacts>:int=
    set H.N+=1
    set H.Trace+=Tag
    Print(Tag)
    Value
Tell(Tag:string,Value:int)<transacts>:int=(Print(Tag);Value)
base:=class:
    H:cell
    A:int=Tell("A",1)
pack:=class(base):
    B:int
    C:int=Tell("C",3)
    D:int
    T:int=Tell("T",9)
    block:
        Mark(H,"K",0)
failpack:=class(pack):
    T<override>:int=Err()
Direct(H:cell,P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:pack=
    pack{D:=Mark(H,"D",0)+dup[Q].C,B:=Mark(H,"B",0)+dup[P].C,H:=H}
Named(H:cell,P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:pack=
    A:=Tell("A",1)
    B:=Mark(H,"B",0)
    X:=dup[P]
    C:=Tell("C",3)
    D:=Mark(H,"D",0)
    Y:=dup[Q]
    T:=Tell("T",9)
    pack{D:=D+Y.C,H:=H,T:=T,B:=B+X.C,C:=C,A:=A}
DirectFail(H:cell,P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:failpack=
    failpack{D:=Mark(H,"D",0)+dup[Q].C,B:=Mark(H,"B",0)+dup[P].C,H:=H}
NamedFail(H:cell,P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:failpack=
    A:=Tell("A",1)
    B:=Mark(H,"B",0)
    X:=dup[P]
    C:=Tell("C",3)
    D:=Mark(H,"D",0)
    Y:=dup[Q]
    failpack{D:=D+Y.C,H:=H,B:=B+X.C,C:=C,A:=A}
Main()<transacts>:void=
    H:=cell{}
    K:=cell{}
    Good:pair(int,int)=dup(int){}
    Bad:pair(int,int)=pair(int,int){}
    if(V:=Direct[H,Good,Good]) then Print("direct {V.A} {V.B} {V.C} {V.D} {V.T} {H.N} {H.Trace}") else Print("wrong")
    if(V:=Named[K,Good,Good]) then Print("named {V.A} {V.B} {V.C} {V.D} {V.T} {K.N} {K.Trace}") else Print("wrong")
    if(V:=DirectFail[H,Bad,Good]) then Print("wrong") else Print("lower {H.N} {H.Trace}")
    if(V:=NamedFail[K,Bad,Good]) then Print("wrong") else Print("lower named {K.N} {K.Trace}")
    if(V:=DirectFail[H,Good,Bad]) then Print("wrong") else Print("upper {H.N} {H.Trace}")
    if(V:=NamedFail[K,Good,Bad]) then Print("wrong") else Print("upper named {K.N} {K.Trace}")
