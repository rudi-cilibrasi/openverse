Pick(V:t,Stop:logic where t:type)<computes>:t=
    Y:=if(Stop?)then(return V)else V
    Y|Y
R(N:int)<computes>:int=
    Y:=if(N=2)then(return N*10)else N
    if(N>0)then(R(N-1)|Y)else(0|1)
Main():void=
    for(V:=Pick(7,true)){Print("i {V}")}
    for(V:=Pick("a",false)){Print("s {V}")}
    for(V:=R(3)){Print("a {V}")}
    for(V:=R(1)){Print("b {V}")}
    Print("after")
