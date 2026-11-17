Send(E:event(t), Value:t where t:type)<transacts>:void =
    E.Signal(Value)

Main():void =
    E := event(int){}
    if (Send(E, 1), false?):
        Print("OVPROBE unexpected")
    Print("OVPROBE after")
