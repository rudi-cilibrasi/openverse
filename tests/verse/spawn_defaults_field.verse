# (run with --default-rollback, the legacy rule: by default a spawn has the no_rollback effect, which this program's spawn's context excludes, UEFN 43.12 error 3512, #724)
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
