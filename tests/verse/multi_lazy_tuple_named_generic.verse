Walk(X:a,Y:b,N:int,?D:a=block{ E:[]a=array{X}; E[0] } where a:type,b:type)<transacts><decides>:a =
    N>0
    Print("visit {N}")
    D | Walk[(X,Y,N-1)]
Run(X:b,Y:a where a:type,b:type)<transacts>:[]b = for(V:=Walk[X,Y,2]): V
First(X:b,Y:a where a:type,b:type)<transacts>:?b = option{Walk[X,Y,2]}
Main()<transacts>:void =
    for(V:Run(7,"s")){Print("{V}")}
    for(V:Run("s",7)){Print(V)}
    if(V:=First(7,"s")?)then Print("first {V}")
    if(V:=First("s",7)?)then Print("first {V}")
