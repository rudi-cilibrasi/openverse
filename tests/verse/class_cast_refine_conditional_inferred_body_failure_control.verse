expr(t:type) := class<abstract>:
    Eval()<transacts>:t
lit := class(expr(int)):
    V:int
    Eval<override>()<transacts>:int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>()<transacts>:tuple(a, b) = (L.Eval(), R.Eval())
cell:=class{var N:int=0}
RowsBody(E:expr(tuple(int,int)),H:cell,Reject:int)<transacts><decides>:[]tuple(int,int)=
    for(N:=1..2,V:=if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then((L.V,R.V)|(L.V+1,R.V))else E.Eval()):
        set H.N+=1
        Print("body {H.N}")
        H.N<>Reject
        V

RowsPrefix(E:expr(tuple(int,int)),H:cell,Reject:int)<transacts><decides>:[]tuple(int,int)=
    for(0=1,N:=1..2,V:=if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then((L.V,R.V)|(L.V+1,R.V))else E.Eval()):
        set H.N+=1
        Print("body {H.N}")
        H.N<>Reject
        V

RowsSuffix(E:expr(tuple(int,int)),H:cell,Reject:int)<transacts><decides>:[]tuple(int,int)=
    for(N:=1..2,V:=if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then((L.V,R.V)|(L.V+1,R.V))else E.Eval(),N=9):
        set H.N+=1
        Print("body {H.N}")
        H.N<>Reject
        V

RowsSelected(E:expr(tuple(int,int)),H:cell,Reject:int)<transacts><decides>:[]tuple(int,int)=
    for(N:=1..2,V:=if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then((L.V,R.V)|(L.V+1,R.V))else E.Eval(),N=1):
        set H.N+=1
        Print("body {H.N}")
        H.N<>Reject
        V

CaseBody()<transacts>:void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    A:=cell{}
    if(Values:=RowsBody[P,A,99]):
        for(V:Values){Print("v {V(0)} {V(1)}")}
    else Print("bad")
    Print("after {P.L.Eval()} {A.N}")
    Q:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    B:=cell{}
    if(ValuesB:=RowsBody[Q,B,2])then Print("bad")else Print("rejected {Q.L.Eval()} {B.N}")

CasePrefix()<transacts>:void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    A:=cell{}
    if(Values:=RowsPrefix[P,A,99]):
        for(V:Values){Print("v {V(0)} {V(1)}")}
    else Print("bad")
    Print("after {P.L.Eval()} {A.N}")
    Q:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    B:=cell{}
    if(ValuesB:=RowsPrefix[Q,B,2])then Print("empty {ValuesB.Length} {Q.L.Eval()} {B.N}")else Print("rejected {Q.L.Eval()} {B.N}")

CaseSuffix()<transacts>:void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    A:=cell{}
    if(Values:=RowsSuffix[P,A,99]):
        for(V:Values){Print("v {V(0)} {V(1)}")}
    else Print("bad")
    Print("after {P.L.Eval()} {A.N}")
    Q:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    B:=cell{}
    if(ValuesB:=RowsSuffix[Q,B,2])then Print("empty {ValuesB.Length} {Q.L.Eval()} {B.N}")else Print("rejected {Q.L.Eval()} {B.N}")

CaseSelected()<transacts>:void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    A:=cell{}
    if(Values:=RowsSelected[P,A,99]):
        for(V:Values){Print("v {V(0)} {V(1)}")}
    else Print("bad")
    Print("after {P.L.Eval()} {A.N}")
    Q:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    B:=cell{}
    if(ValuesB:=RowsSelected[Q,B,2])then Print("empty {ValuesB.Length} {Q.L.Eval()} {B.N}")else Print("rejected {Q.L.Eval()} {B.N}")
Main()<transacts>:void=
    CaseBody()
    CasePrefix()
    CaseSuffix()
    CaseSelected()
