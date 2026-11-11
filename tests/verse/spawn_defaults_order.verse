Note(S:string,N:int):int=block{Print("{S} {N}");N}
Tick(S:string,X:t where t:type):t=block{Print(S);X}
base(t:type) := class:
    Go(X:t,?A:int=0,?B:int=0,?C:int=0)<suspends>:int=C
ib := class(base(int)):
    var Calls:int=0
    Seed:int=4
    Go<override>(X:int,?A:int=block{set Calls+=1;Note("default A",Seed+X)},?B:int=block{set Calls+=1;Note("default B",A+1)},?C:int=block{set Calls+=1;Note("default C",B+1)})<suspends>:int=
        Print("body {X} {A} {B} {C}")
        Sleep(0.01)
        C
Start(P:base(t),X:t where t:type):task(int)=
    T:=spawn{Tick("receiver",P).Go(Tick("positional",X),?B:=Note("given B",9),?A:=Note("given A",7))}
    Print("spawned")
    T
Main()<suspends>:void=
    C:=ib{}
    T:=Start(C,3)
    Print("result {T.Await()} {C.Calls}")
