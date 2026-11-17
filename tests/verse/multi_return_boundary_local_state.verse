F(X:int)<transacts>:int=
    var N:int=0
    var Flag:logic=false
    for(I:=1..X):
        defer:set N+=10
        set N+=I
        set Flag=true
        if(I=2):return N
    if(Flag?)then(N|N+1)else(90|91)
Main()<transacts>:void=
    for(V:=F(3)){Print("a {V}")}
    for(V:=F(1)){Print("b {V}")}
    for(V:=F(0)){Print("c {V}")}
    if(V:=F(1),V=12)then Print("first {V}")else Print("bad")
