F(X:int)<computes>:?int=
    for(I:=1..X):
        if(I=2):return false
    Y:?int=if(X=1)then(return option{7})else false
    Y|option{8}
Main():void=
    for(X:array{3,1,0}):
        for(V:=F(X)):
            if(N:=V?)then Print("{X} some {N}")else Print("{X} none")
