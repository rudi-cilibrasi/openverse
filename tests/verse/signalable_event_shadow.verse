signalable(t:type) := interface:
    Read():t

counter := class(signalable(int)):
    Read<override>():int = 7

Main():void =
    N:signalable(int) = counter{}
    E := event(int){}
    E.Signal(N.Read())
    Print("{N.Read()}")
