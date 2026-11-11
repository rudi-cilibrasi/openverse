base(t:type) := class:
    Go(?N:int=0)<suspends>:int=N
ib := class(base(int)):
    Seed:int=3
    Go<override>(?N:int=block{Print("default {Seed}");Seed})<suspends>:int=block{Sleep(0.01);N}
AsBase(P:base(t) where t:type):base(t)=P
unused := struct:
    Job:task(int)=spawn{AsBase(ib{}).Go()}
record := struct:
    Job:task(int)=spawn{AsBase(ib{}).Go()}
Main()<suspends>:void=
    A:=record{}
    B:=record{}
    C:=record{Job:=A.Job}
    Print("created")
    Print("results {A.Job.Await()} {B.Job.Await()} {C.Job.Await()}")
