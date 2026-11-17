F(Stop:logic)<transacts>:int=
    var N:int=2
    loop:
        defer:Print("cleanup {N}")
        if(Stop?)then break else return N|N+1
    9|10
Main()<transacts>:void=
    for(V:=F(true)){Print("break {V}")}
    for(V:=F(false)){Print("return {V}")}
    if(V:=F(false),V=3)then Print("first {V}")else Print("bad")
