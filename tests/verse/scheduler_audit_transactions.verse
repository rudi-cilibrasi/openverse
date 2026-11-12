handler:=class:
    var N:int=0
    Add(V:int):void=
        set N+=V
        Print("handler {V} {N}")
Waiter(E:subscribable_event(int))<suspends>:void=
    V:=E.Await()
    Print("await {V}")
Main()<suspends>:void=
    E:=subscribable_event(int){}
    H:=handler{}
    K:=E.Subscribe(H.Add)
    W:=spawn{Waiter(E)}
    if(E.Signal(1),false?):Print("wrong signal")
    Print("rollback {H.N}")
    E.Signal(2)
    W.Await()
    if(K.Cancel(),false?):Print("wrong cancel")
    E.Signal(3)
    if(Temp:=E.Subscribe(H.Add),false?):Print("wrong subscribe")
    E.Signal(4)
    K.Cancel()
    E.Signal(5)
    Print("final {H.N}")
