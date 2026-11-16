F(X:int)<transacts>:int=
    var Y:int=if(X<2)then(1|2)else(return 0)
    defer:
        Print("cleanup {Y}")
        set Y+=10
    Y|Y+1
Main()<transacts>:void=
    for(V:=F(0)){Print("v {V}")}
    for(V:=F(3)){Print("early {V}")}
    Print("after")
