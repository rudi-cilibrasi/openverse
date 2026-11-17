counter := class:
    var Last:int = 0

    Receive(N:int)<transacts>:void =
        set Last = N

Main():void =
    E := event(int){}
    C := counter{}
    Subscription := E.Subscribe(C.Receive)
    E.Signal(2)
    Print("OVPROBE after success {C.Last}")
    Subscription.Cancel()
