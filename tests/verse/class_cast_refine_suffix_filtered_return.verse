expr(t:type):=class<abstract>{Eval()<transacts>:t}
lit:=class(expr(int)){V:int;Eval<override>()<transacts>:int=V}
vpair(a:type,b:type):=class(expr(tuple(a,b))){var L:expr(a);R:expr(b);Eval<override>()<transacts>:tuple(a,b)=(L.Eval(),R.Eval())}
Run(E:expr(t) where t:type)<transacts>:[]t=
    Ignored:[]t=for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>1):
        Print("body")
        if(N=2)then return array{}
        (L.V,R.V)
    array{}
Main()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    Rows:=Run(E)
    Print("rows {Rows.Length}")
    Print("state {E.L.Eval()}")
