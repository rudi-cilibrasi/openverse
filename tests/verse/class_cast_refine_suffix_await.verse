expr(t:type):=class<abstract>{Eval()<transacts>:t}
lit:=class(expr(int)){V:int;Eval<override>()<transacts>:int=V}
vpair(a:type,b:type):=class(expr(tuple(a,b))){var L:expr(a);R:expr(b);Eval<override>()<transacts>:tuple(a,b)=(L.Eval(),R.Eval())}
Run(E:expr(t),Ev:event(int),Limit:int where t:type)<suspends>:[]t=
    for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>Limit):
        Ev.Await()
        (L.V,R.V)
Main()<suspends>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    Ev:=event(int){}
    Empty:=Run(E,Ev,2)
    Print("empty {Empty.Length} state {E.L.Eval()}")
    branch:
        Sleep(0.1)
        Ev.Signal(1)
        Sleep(0.1)
        Ev.Signal(2)
    Rows:=Run(E,Ev,0)
    Print("rows {Rows.Length}")
    Print("state {E.L.Eval()}")
