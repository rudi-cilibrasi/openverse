# Index casts refine generic RHS values and preserve the value returned by
# assignment, including bindings, ordinary arguments and constructor fields.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
box(t:type):=struct{Value:t}
Id(X:t where t:type):t=X
Direct(P:pair(a,b) where a:type,b:type)<decides>:b=
    var A:[]b=array{P.B}
    set A[dup[P].Index]=P.A
    A[0]
Named(P:pair(a,b) where a:type,b:type)<decides>:b=
    var A:[]b=array{P.B}
    D:=dup[P]
    set A[D.Index]=P.A
    A[0]
Result(P:pair(a,b) where a:type,b:type)<decides>:tuple(b,b)=
    var A:[]b=array{P.B}
    R:=set A[dup[P].Index]=P.A
    (R,A[0])
Argument(P:pair(a,b) where a:type,b:type)<decides>:b=
    var A:[]b=array{P.B}
    Id(set A[dup[P].Index]=P.A)
Field(P:pair(a,b) where a:type,b:type)<decides>:box(b)=
    var A:[]b=array{P.B}
    box(b){Value:=set A[dup[P].Index]=P.A}
Map(P:pair(a,b) where a:type,b:type)<decides>:b=
    var A:[int]b=map{0=>P.B}
    set A[dup[P].Index]=P.A
    A[0]
Main():void=
    I:=dup(int){A:=7,B:=9}
    S:=dup(string){A:="left",B:="right"}
    if(V:=Direct[I],W:=Named[I],R:=Result[I],A:=Argument[I],F:=Field[I],M:=Map[I])then Print("int {V} {W} {R(0)} {R(1)} {A} {F.Value} {M}")else Print("wrong")
    if(V:=Direct[S],W:=Named[S],R:=Result[S],A:=Argument[S],F:=Field[S],M:=Map[S])then Print("string {V} {W} {R(0)} {R(1)} {A} {F.Value} {M}")else Print("wrong")
    if(V:=Direct[pair(int,string){A:=1,B:="other"}])then Print("wrong")else Print("missing")
    if(V:=Direct[dup(int){A:=7,B:=9,Index:=3}])then Print("wrong")else Print("out of range")
