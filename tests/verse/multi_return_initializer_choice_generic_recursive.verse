Pick(V:t,Stop:logic where t:type)<computes>:t=
    Y:=if(Stop?)then(return V)else(V|V)
    Y|Y
R(N:int)<computes>:int=
    Y:=if(N=2)then(return N*10)else(N|N+1)
    if(N>0)then(R(N-1)|Y)else(Y|Y+10)
Different(X:int)<computes>:int=
    Y:=if(X>2)then(return 0)else("a"|"bbb")
    Y.Length|Y.Length+10
Main():void=
    for(V:=Pick(7,true)){Print("i {V}")}
    for(V:=Pick("s",false)){Print("s {V}")}
    for(V:=R(3)){Print("r3 {V}")}
    for(V:=R(1)){Print("r1 {V}")}
    for(V:=Different(3)){Print("d3 {V}")}
    for(V:=Different(1)){Print("d1 {V}")}
