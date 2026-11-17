F(N:int)<computes>:int=
    for(I:=1..2):
        for(J:=1..2):
            for(K:=1..2):
                for(L:=1..2):
                    if(I=2,J=2,K=2,L=2):return N|N+1
    N+10|N+11
Main()<transacts>:void=
    for(V:=F(2)):Print("all {V}")
    if(V:=F(2),V=3)then Print("first {V}")else Print("bad")
    if(V:=F(2),V=99)then Print("bad")else Print("none")
