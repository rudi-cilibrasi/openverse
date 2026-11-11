pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int =
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]
product := class { N:int=0 }
Make<constructor>() := product:
    N:=block{loop{for(A:array{1,2},if(A=1)then break else 0):Print("bad body");Print("bad loop")};42}
Main():void=Print("result {Make().N}")
