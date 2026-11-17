F(X:int)<transacts>:int=
    for(I:=1..X):
        Y:=I|I+1
        if(I=2):return Y
    X|X+1
Main()<transacts>:void=for(V:=F(3)){Print("{V}")}
