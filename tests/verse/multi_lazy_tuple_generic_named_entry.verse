Repeat(X:t,N:int,?Y:t=X where t:type)<transacts>:t =
    Print("visit {N}")
    if(N>0)then(Y | Repeat((X,N-1)))else Y
All(X:a,Y:a where a:type)<transacts>:[]a =
    P:tuple(a,int)=(X,2)
    for(V:=Repeat(P,?Y:=Y)): V
First(X:a,Y:a where a:type)<transacts>:?a =
    P:tuple(a,int)=(X,2)
    option{Repeat(P,?Y:=Y)}
box(t:type) := class:
    Value:t
    Walk(E:[]t,N:int,?D:t=Value)<transacts>:t =
        Print("method {N}")
        if(N>0)then(D | Walk((array{},N-1)))else D
Main()<transacts>:void =
    for(V:All(7,9)){Print("all {V}")}
    for(V:All("s","t")){Print("all {V}")}
    if(V:=First(7,9)?)then Print("first {V}")
    if(V:=First("s","t")?)then Print("first {V}")
    for(V:=box(string){Value:="s"}.Walk((array{},2),?D:="t")){Print("method {V}")}
