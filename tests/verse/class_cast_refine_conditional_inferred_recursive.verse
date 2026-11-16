expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
counter:=class{var N:int=0}
Read(H:counter,V:int)<transacts>:int={set H.N+=1;V}
Pairs(L:int,R:int,N:int)<computes><decides>:tuple(int,int)=
    N>=0
    (L,R)|Pairs[L+1,R,N-1]
Rows(E:expr(t),H:counter where t:type)<transacts>:[]t=for(N:=1..2,V:=if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then Pairs[Read(H,L.V),Read(H,R.V),1]else E.Eval()){V}
Main()<transacts>:void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    H:=counter{}
    for(V:Rows(P,H)){Print("{V(0)} {V(1)}")}
    Print("final {P.L.Eval()} reads {H.N}")
