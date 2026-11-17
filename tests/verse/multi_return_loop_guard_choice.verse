Pick(N:int)<transacts>:int=
    for(I:=1..N):
        if(Y:=I|I+1,Y=2):
            defer:Print("cleanup {I} {Y}")
            return Y|Y+10
    N|N+1
Main()<transacts>:void=
    for(V:=Pick(3)):Print("all {V}")
    if(V:=Pick(3),V=12)then Print("first {V}")else Print("missed")
    if(V:=Pick(3),V=999)then Print("bad")else Print("none")
    for(V:=Pick(0)):Print("fallback {V}")
