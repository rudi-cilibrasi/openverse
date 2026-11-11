# expect: needs the argument ?Step, which has no default
Walk(A:int,B:int,N:int,?Step:int)<computes>:int = if(N>0) then (A | Walk((B,A,N-Step))) else A
Main():void = for(V:=Walk(3,4,2,?Step:=1)){Print("{V}")}
