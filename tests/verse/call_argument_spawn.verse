# Packed values/defaults are bound before spawn; cancellation unwinds once.
state:=class:
    var N:int=0
Mark(S:state,Name:string,V:int):int=
    set S.N+=1
    Print("{Name} {S.N}")
    V
Go(P:tuple(int,int),?B:int,?A:int=block{Print("default {P(0)} {B}");P(1)+B})<suspends>:void=
    defer{Print("cleanup {A}")}
    Print("body {P(0)} {P(1)} {B} {A}")
    Sleep(Inf)
worker:=class:
    (worker:)Go(P:tuple(int,int),?B:int,?A:int=0)<suspends>:void=Print("base")
child:=class(worker):
    Go<override>(P:tuple(int,int),?B:int,?A:int=block{Print("method default");P(1)+B})<suspends>:void=
        defer{Print("method cleanup {A}")}
        Print("method {P(0)} {P(1)} {B} {A}")
        Sleep(Inf)
Receiver(S:state):worker=
    set S.N+=1
    Print("receiver {S.N}")
    child{}
Main()<suspends>:void=
    S:=state{}
    T:=spawn{Go(Mark(S,"left",1),Mark(S,"right",2),?B:=Mark(S,"named",3))}
    Print("spawned {S.N}")
    T.Cancel()
    U:=spawn{Receiver(S).Go(Mark(S,"mleft",4),Mark(S,"mright",5),?B:=Mark(S,"mnamed",6))}
    Print("spawned method {S.N}")
    U.Cancel()
