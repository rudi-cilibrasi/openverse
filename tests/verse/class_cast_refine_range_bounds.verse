# Both ordered bounds can refine separate type arguments. The body has an
# aggregate generic result. Named casts give the same values and failures.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)):
    Lo:int=1
    Hi:int=2
Direct(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type):[]tuple(int,b,d)=
    for(I:=dup[P].Lo+0..dup[Q].Hi+0){(I,P.A,Q.A)}
Named(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type):[]tuple(int,b,d)=
    if(D:=dup[P]):
        if(E:=dup[Q]) then for(I:=D.Lo+0..E.Hi+0){(I,P.A,Q.A)} else array{}
    else:
        array{}
Lower(P:pair(a,b) where a:type,b:type):[]int=for(I:=dup[P].Lo..3){I}
Upper(P:pair(a,b) where a:type,b:type):[]int=for(I:=0..dup[P].Hi){I}
Main():void=
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    Bad:pair(int,string)=pair(int,string){A:=1,B:="other"}
    for(V:Direct(P,Q)){Print("direct {V(0)} {V(1)} {V(2)}")}
    for(V:Named(P,Q)){Print("named {V(0)} {V(1)} {V(2)}")}
    for(V:Lower(P)){Print("lower {V}")}
    for(V:Upper(P)){Print("upper {V}")}
    Print("missing {Direct(Bad,Q).Length} {Named(Bad,Q).Length} {Direct(P,Bad).Length} {Named(P,Bad).Length}")
    Print("empty {Direct(dup(int){A:=7,B:=9,Lo:=3},Q).Length} {Named(dup(int){A:=7,B:=9,Lo:=3},Q).Length}")
    Print("single missing {Lower(Bad).Length} {Upper(Bad).Length}")
