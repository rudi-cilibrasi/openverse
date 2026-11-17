InitializerReturn(X:int)<transacts>:int=
    Y:=if(X>2)then(return 0)else(X|X+1)
    Y|Y+1
Main()<transacts>:void=
    for(V:=InitializerReturn(3)){Print("i3 {V}")}
    for(V:=InitializerReturn(1)){Print("i1 {V}")}
    if(V:=InitializerReturn(1),V=3)then Print("first {V}")else Print("bad")
    Print("after")
