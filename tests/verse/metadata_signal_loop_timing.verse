One()<computes>:int=1
Two()<computes>:int=2
EventWorker(E:event(int))<suspends>:int=E.Await()

LoopTasks(SignalFirst:logic)<suspends>:int=
    A:=event(int){}
    B:=event(int){}
    Other:=event(int){}
    var Selected:event(int)=A
    Tasks:=for(N:=0..1):
        T:=spawn{EventWorker(Selected)}
        set Selected=B
        T
    var Stored:type{_()<computes>:int}=Two
    if(T:=Tasks[0]):
        branch:
            T.Await()
            set Stored=Two
        set Stored=One
        if(SignalFirst?)then A.Signal(0)else Other.Signal(0)
        Stored()
    else:
        0

Main()<suspends>:void=
    Print("loop task {LoopTasks(true)}")
    Print("loop unrelated {LoopTasks(false)}")
