box:=class<computes>:
    Bias<private>:int=10
    Run<public>(N:int)<computes>:int=
        if(N>=2):return Bias+2|Bias+3
        Bias|Bias+1
Main():void=
    B:=box{}
    for(V:=B.Run(3)){Print("value {V}")}
    if(V:=B.Run(3),V=13)then Print("first {V}")else Print("bad")
    Print("after")
