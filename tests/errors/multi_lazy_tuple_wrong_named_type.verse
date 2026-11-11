# expect: expected int, found string
Walk(A:int,B:int,N:int,?Step:int=1)<computes>:int = if(N>0) then (A | Walk((B,A,N-Step),?Step:="bad")) else A
Main():void = for(V:=Walk(3,4,2)){Print("{V}")}
