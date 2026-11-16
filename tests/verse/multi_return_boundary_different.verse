F(X:int)<transacts>:int=
    Y:=if(X>2)then(return 0)else "ok"
    Y.Length|Y.Length+1
Main()<transacts>:void=
    for(V:=F(3)){Print("a {V}")}
    for(V:=F(1)){Print("b {V}")}
    Print("after")
