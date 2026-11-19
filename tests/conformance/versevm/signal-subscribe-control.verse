counter := class:
    var Seen:int = 0

    Receive(N:int)<transacts>:void =
        set Seen = N

Main():void =
    E := event(int){}
    C := counter{}
    Subscription := E.Subscribe(C.Receive)
    E.Signal(2)
    Print("OVPROBE after success {C.Seen}")
    Subscription.Cancel()
