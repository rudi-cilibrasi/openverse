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
    if(V:=Walk(3,C),V=1)then Print("first {V} {C.N}")
    if(V:=Walk(2,C),V<0)then Print("bad")else Print("none {C.N}")
    O:=option{V:=Walk(3,C);V=2;V}
    if(V:=O?)then Print("option {V} {C.N}")
    L:=logic{V:=Walk(1,C);V<0}
    Print("after logic {C.N}")
    if(not(V:=Walk(1,C);V<0))then Print("not {C.N}")
    V:=first{X:=Walk(2,C);X=1;X} or 99
    Print("or {V} {C.N}")
