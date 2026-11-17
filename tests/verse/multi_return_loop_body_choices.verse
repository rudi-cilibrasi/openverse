Pick(Count:int)<transacts>:int=
    for(I:=1..Count):
        Y:=I|I+1
        defer:Print("cleanup {I} {Y}")
        if(I=2):return Y
    Count
Overflow(N:int)<computes>:int=9223372036854775807+N
PickEarly()<computes>:int=
    for(I:=1..9223372036854775807):
        Y:=I|Overflow(I)
        if(I=1):return Y
    0
Main()<transacts>:void=
    for(V:=Pick(3)):Print("all {V}")
    if(V:=Pick(3),V=3)then Print("first {V}")else Print("missed")
    if(V:=Pick(3),V=999)then Print("bad")else Print("none")
    for(V:=Pick(1)):Print("suffix {V}")
    if(V:=PickEarly(),V=1)then Print("first unused {V}")else Print("missed")
