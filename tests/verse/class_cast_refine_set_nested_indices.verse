# Separate casts in both path indices refine the RHS. A failed first index
# skips an erroneous second-index operand; the assignment result is kept.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
Second(Stop:logic):int=if(Stop?)then Err()else 0
Direct(P:pair(a,b),Q:pair(c,d),Stop:logic where a:type,b:type,c:type,d:type)<decides>:tuple(d,d)=
    var A:[][]d=array{array{Q.B}}
    R:=set A[dup[P].Index][Second(Stop)+dup[Q].Index]=Q.A
    (R,A[0][0])
Named(P:pair(a,b),Q:pair(c,d),Stop:logic where a:type,b:type,c:type,d:type)<decides>:tuple(d,d)=
    var A:[][]d=array{array{Q.B}}
    D:=dup[P]
    I:=D.Index
    J:=Second(Stop)
    E:=dup[Q]
    R:=set A[I][J+E.Index]=Q.A
    (R,A[0][0])
Main():void=
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    Bad:pair(int,int)=pair(int,int){A:=1,B:=2}
    if(V:=Direct[P,Q,false],W:=Named[P,Q,false])then Print("nested {V(0)} {V(1)} / {W(0)} {W(1)}")else Print("wrong")
    if(V:=Direct[Bad,Q,true])then Print("wrong")else Print("missing outer")
    if(V:=Direct[P,Bad,false])then Print("wrong")else Print("missing inner")
    if(V:=Direct[dup(int){A:=7,B:=9,Index:=2},Q,false])then Print("wrong")else Print("outer bounds")
    if(V:=Direct[P,dup(string){A:="left",B:="right",Index:=2},false])then Print("wrong")else Print("inner bounds")
