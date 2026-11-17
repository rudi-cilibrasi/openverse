F(X:int)<transacts>:int=
    for(I:=1..X):
        if(I=2):return I
    X|X+1
G(X:int)<transacts>:int=
    for(V:=F(X)):return V+10
    999
Main()<transacts>:void=
    Print("g {G(3)}")
    Print("g {G(1)}")
    Print("after")
