F(N:int)<computes>:int=
    for(I:=1..N):
        for(J:=1..2):
            if(I=2,J=2):return I+J|I+J+1
    9|10
Main():void=
    for(V:=F(3)){Print("v {V}")}
    for(V:=F(0)){Print("zero {V}")}
    if(V:=F(3),V=5)then Print("first {V}")else Print("bad")
    if(V:=F(3),V=999)then Print("bad")else Print("none")
