Bounds()<computes>:int= -9223372036854775808|-10
Pick()<computes>:int=
    for(I:=Bounds()..9223372036854775807,J:=0..1):
        if(I<0,J=1):return I|I+1
    -1|-2
Main():void=
    for(V:=Pick()):Print("all {V}")
    if(V:=Pick(),V= -9223372036854775807)then Print("first {V}")else Print("missed")
