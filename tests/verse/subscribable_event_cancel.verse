# subscribable_event (#220): a function cancelled during a Signal, by one
# called before it, is not called by it, while one cancelled by a later
# function was already called; a Signal in a failure context is rolled
# back with what its functions did
holder := class:
    var Victim:?cancelable = false
    var Calls:int = 0
    First(X:int):void =
        set Calls += 1
        Print("first {X}")
        if (V := Victim?) then V.Cancel()
Second(X:int):void = Print("second {X}")
Third(X:int):void = Print("third {X}")
Main():void =
    E := subscribable_event(int){}
    H := holder{}
    A := E.Subscribe(H.First)
    B := E.Subscribe(Second)
    set H.Victim = option{B}
    E.Signal(1)
    E.Signal(2)
    F := subscribable_event(int){}
    G := holder{}
    C := F.Subscribe(Third)
    D := F.Subscribe(G.First)
    set G.Victim = option{C}
    F.Signal(3)
    F.Signal(4)
    if (E.Signal(5), 1 > 2) then Print("no") else Print("rolled back")
    Print("calls {H.Calls}")
