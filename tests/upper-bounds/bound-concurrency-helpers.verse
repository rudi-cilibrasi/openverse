car:=class<computes>{Name:string="precise"}
counter:=class<allocates>{var N:int=0}
Take(X:t,C:counter where t:type)<transacts>:t=(set C.N+=1;X)
AwaitEvent(E:t,C:counter where t:subtype(event(int)))<suspends>:int=Take(E,C).Await()
AwaitTask(T:t,C:counter where e:type,t:subtype(task(e)))<suspends>:e=Take(T,C).Await()
CancelTask(T:t,C:counter where t:subtype(task(int)))<suspends>:void=Take(T,C).Cancel()
SignalUnit(E:t,C:counter where t:subtype(event(void)))<transacts>:void=Take(E,C).Signal()
AwaitUnit(E:t,C:counter where t:subtype(event(void)))<suspends>:void=Take(E,C).Await()
AwaitSticky(E:t,C:counter where t:subtype(sticky_event(int)))<suspends>:int=Take(E,C).Await()
Value()<suspends>:car=(Sleep(0.01);car{})
Leaf()<suspends>:int=
    defer:Print("cleanup")
    Sleep(1.0)
    1
Main()<suspends>:void=
    C:=counter{}
    E:=event(int){}
    W:=spawn{AwaitEvent(E,C)}
    Sleep(0.0)
    E.Signal(7)
    Print("event {W.Await()} {C.N}")
    T:=spawn{Value()}
    V:=AwaitTask(T,C)
    Print("task {V.Name} {C.N}")
    S:=sticky_event(int){}
    S.Signal(9)
    Print("sticky {AwaitSticky(S,C)} {C.N}")
    U:=event(void){}
    Q:=spawn{AwaitUnit(U,C)}
    Sleep(0.0)
    SignalUnit(U,C)
    Q.Await()
    Print("unit {C.N}")
    L:=spawn{Leaf()}
    Sleep(0.0)
    CancelTask(L,C)
    Print("cancel {C.N}")
