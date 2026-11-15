# Regression #653 review: unchanged prepared return clauses retain spatial argument order.
Dup(V:t where t:type):t=V|V
Ov(N:int):int=N+1|N*2
Ov(N:int,M:int):int=N-M|M*3
Take(N:int):int=
    Y:=N|N+1
    Print("p{Y}")
    if(Y=N+1):return 99|98
    Y
Main():void=
    if(A:=Dup(0)|Dup(1),B:=Take(Ov(-1))):Print("value {B}")
