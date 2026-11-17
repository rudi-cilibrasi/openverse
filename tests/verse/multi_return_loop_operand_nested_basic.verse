F(N:int)<transacts>:int=
    var I:int=0
    loop:
        set I+=1
        if(N=0):break
        var J:int=0
        loop:
            set J+=1
            if(J=2):return N|N+1
    9|10
Main()<transacts>:void=
    for(V:=F(2)){Print("v {V}")}
    for(V:=F(0)){Print("zero {V}")}
    if(V:=F(2),V=3)then Print("first {V}")else Print("bad")
    if(V:=F(2),V=999)then Print("bad")else Print("none")
