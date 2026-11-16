Pick(V:t,Stop:logic where t:type)<computes>:[]t=
    if(Stop?):return array{V}
    array{V,V,V,V}
R(N:int)<computes>:[]int=
    if(N=2):return array{N*10}
    Rows:=for(Y:array{N,N+1}):
        if(N>0)then(R(N-1)+array{Y})else array{Y,Y+10}
    for(Row:Rows,V:Row){V}
Different(X:int)<computes>:[]int=
    if(X>2):return array{0}
    array{1,11,3,13}
Main():void=
    for(V:Pick(7,true)){Print("i {V}")}
    for(V:Pick("s",false)){Print("s {V}")}
    for(V:R(3)){Print("r3 {V}")}
    for(V:R(1)){Print("r1 {V}")}
    for(V:Different(3)){Print("d3 {V}")}
    for(V:Different(1)){Print("d1 {V}")}
