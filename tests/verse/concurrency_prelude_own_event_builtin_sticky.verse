event(t:type):=class:
    N:int=7
    Signal(X:t):void=Print("user {N}")
Main()<suspends>:void=
    U:=event(int){}
    U.Signal(1)
    E:=sticky_event(int){}
    E.Signal(3)
    Print("sticky {E.Await()}")
