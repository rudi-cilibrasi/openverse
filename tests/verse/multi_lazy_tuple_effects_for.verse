counter := class { var N:int=0 }
Next(N:int,C:counter)<transacts>:int =
    set C.N+=1
    Print("edge {N}")
    N-1
Walk(N:int,C:counter)<transacts>:int =
    Print("visit {N}")
    if(N>0) then (N | Walk((Next(N,C),C))) else 0
Main()<transacts>:void =
    C:=counter{}
    for(V:=Walk(3,C),V>0){Print("body {V} {C.N}")}
    Print("after {C.N}")
    for(I:=0..1,V:=Walk(2,C),V=1){Print("nested {I} {V} {C.N}")}
    Print("done {C.N}")
