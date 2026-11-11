base(t:type) := class:
    Go(?A:int=0,?B:int=0)<suspends>:void=Print("base")
ib := class(base(int)):
    Go<override>(?A:int=block{Print("default A");3},?B:int=block{Print("default B {A}");A+1})<suspends>:void=
        Print("body {A} {B}")
        Sleep(0.01)
        Print("done")
Start(P:base(t) where t:type):task(void)=
    T:=spawn{P.Go()}
    Print("spawned")
    T
Main()<suspends>:void=
    T:=Start(ib{})
    T.Await()
