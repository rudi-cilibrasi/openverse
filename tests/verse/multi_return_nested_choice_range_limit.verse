Bounds()<computes>:int=1|2
Pick()<computes>:int=
    for(Outer:array{3,4}):
        for(I:=Bounds()..9223372036854775807):
            if(I=2):return Outer+I|Outer+I+1
    -1|-2
Main():void=
    for(V:=Pick()):Print("all {V}")
    if(V:=Pick(),V=6)then Print("first {V}")else Print("missing")
