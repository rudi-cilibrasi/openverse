F(X:int)<transacts>:int=
    var N:int=0
    loop:
        loop:
            set N+=1
            break
        if(N=X):return N
    X|X+1
Main()<transacts>:void=
    for(V:=F(2)){Print("v {V}")}
    Print("after")
