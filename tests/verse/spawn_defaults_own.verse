Note(N:int):int=block{Print("default {N}");N}
base(t:type) := class:
    Go(?X:v=3 where v:type)<suspends>:int=0
ib := class(base(int)):
    Seed:int=7
    Go<override>(?X:v=Note(Seed) where v:type)<suspends>:int=
        Sleep(0.01)
        2
Start(P:base(t) where t:type):task(int)=spawn{P.Go()}
Main()<suspends>:void=
    T:=Start(ib{})
    Print("started")
    Print("result {T.Await()}")
