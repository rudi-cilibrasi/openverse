Dup(V:t where t:type):t=V|V
Ov(N:int)<transacts>:int=N+1|N*2
Ov(N:int,M:int)<transacts>:int=N-M|M*3
Early(N:int)<transacts>:int=
    Y:=N|N+1
    Print("p{Y}")
    if(Y=N+1):return 99|98
    Y
Two(N:int,V:int)<transacts>:int=N+V|N+V+10
Two(S:string,V:int)<transacts>:int=S.Length+V|S.Length+V+10
First(N:int,Xs:[]int)<transacts>:int=if(X:=Xs[0])then N+X else -9
DT(N:int,?Xs:[]int=for(T:=Early(Ov(-1))){T})<transacts>:int=First(N,Xs)|First(N,Xs)+10
DT(S:string,?Xs:[]int=for(T:=Early(Ov(-1))){T})<transacts>:int=First(S.Length,Xs)|First(S.Length,Xs)+10
Main()<transacts>:void=
    var Count:int=0
    for(A:=Dup(0)|Dup("s"),B:=Two(A,Early(Ov(-1)))):set Count+=1
    Print("for {Count}")
    if(A:=Dup(0)|Dup("s"),B:=Two(A,Early(Ov(-1)))):Print("arg first {B}")
    O:=option{A:=Dup(0)|Dup("s");B:=Two(A,Early(Ov(-1)));B}
    if(X:=O?):Print("arg option {X}")
    if(A:=Dup(0)|Dup("s"),B:=DT(A)):Print("default first {B}")
    D:=option{A:=Dup(0)|Dup("s");B:=DT(A);B}
    if(X:=D?):Print("default option {X}")
    for(A:=Dup(0)|Dup("s"),B:=Two(A,0)):
        if(C:=Early(Ov(-1))):Print("body {B} {C}")
