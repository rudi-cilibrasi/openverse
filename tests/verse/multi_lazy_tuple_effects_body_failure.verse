counter := class { var N:int=0 }
Next(N:int,C:counter)<transacts>:int =
    set C.N+=1
    Print("edge {N}")
    N-1
Walk(N:int,C:counter)<transacts>:int =
    Print("visit {N}")
    if(N>0) then (N | Walk((Next(N,C),C))) else 0
Run(C:counter)<transacts><decides>:void =
    for(V:=Walk(3,C)):
        Print("body {V}")
        V>1
Main()<transacts>:void =
    C:=counter{}
    if(Run[C])then Print("ok")else Print("failed {C.N}")
