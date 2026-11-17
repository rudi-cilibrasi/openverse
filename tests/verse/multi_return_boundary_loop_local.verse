F(X:int)<transacts>:int=
    for(I:=1..X):
        var Inside:int=I
        set Inside+=10
        if(I=2):return Inside
    X|X+1
Main()<transacts>:void=
    for(V:=F(3)){Print("a {V}")}
    for(V:=F(1)){Print("b {V}")}
