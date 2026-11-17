Send(E:event(t), Value:t where t:type)<transacts>:void =
    E.Signal(Value)

Main():void =
    E := event(int){}
    Send(E, 1)
    Print("OVPROBE after")
