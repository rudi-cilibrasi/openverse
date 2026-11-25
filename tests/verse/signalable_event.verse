Send(To:signalable(t), Payload:t where t:type)<transacts>:void =
    To.Signal(Payload)

Main()<suspends>:void =
    E := event(int){}
    View:signalable(int) = E
    branch:
        N := E.Await()
        Print("received {N}")
    Sleep(0.1)
    if (Send(View, 1), false?):
        Print("unexpected")
    Send(View, 2)
    Sticky := sticky_event(string){}
    Send(Sticky, "sticky")
    Print(Sticky.Await())
