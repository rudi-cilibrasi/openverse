counter := class:
    var Seen:int = 0

    Receive(N:int):void =
        set Seen = N

Attach(E:event(int), C:counter)<transacts>:cancelable =
    E.Subscribe(C.Receive)

Main():void =
    E := event(int){}
    C := counter{}
    Subscription := Attach(E, C)
    E.Signal(4)
    Print("OVPROBE seen {C.Seen}")
    Subscription.Cancel()
