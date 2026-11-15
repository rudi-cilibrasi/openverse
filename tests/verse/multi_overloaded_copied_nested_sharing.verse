Dup(V:t where t:type):t=V|V
Pick(N:int):int=N|N+10
Pick(S:string):int=S.Length|S.Length+10
Take(N:int):int=
    Y:=N|N+1
    Print("p{Y}")
    if(Y=N+1):return 99|98
    Y
Main():void=
    for(A:=Dup(1)|Dup("s"),B:=Pick(A)):
        if(C:=Dup(0)|Dup(1),D:=Take(Pick(A))):Print("{B} {D}")
