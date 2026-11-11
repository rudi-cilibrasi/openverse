pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int =
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]
F(?N:int=block{loop{for(A:array{1,2},if(A=1)then break else 0):Print("bad body");Print("bad loop")};42}):int=N
Main():void=Print("result {F()}")
