F(X:int)<transacts>:int=
    loop:return X
    X|X+1
Main()<transacts>:void=
    for(V:=F(7)){Print("v {V}")}
    Print("after")
