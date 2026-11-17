counter := class:
    var Last:int = 0

    Receive(N:int)<transacts>:void =
        set Last = N

Main():void =
    E := event(int){}
    C := counter{}
    Subscription := E.Subscribe(C.Receive)
    if (E.Signal(1), false?):
        Print("OVPROBE unexpected")
    Print("OVPROBE after failure {C.Last}")
    E.Signal(2)
    Print("OVPROBE after success {C.Last}")
    Subscription.Cancel()
