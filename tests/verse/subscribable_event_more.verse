# subscribable_event (#210): a function subscribed during a Signal is first
# called at the next; cancelling twice; Subscribe and Cancel rolled back in
# a failure context; a tuple payload; many subscriptions cancelled (memory
# follows the live ones)
relay := class:
    E:subscribable_event(int)
    var Added:logic = false
    On(X:int):void =
        Print("relay {X}")
        if (Added?) {} else:
            set Added = true
            S := E.Subscribe(Late)
Late(X:int):void = Print("late {X}")
ShowPt(P:tuple(int, string)):void = Print("pt {P(0)} {P(1)}")
ctr := class:
    var N:int = 0
    On(X:int):void = set N += X
Main():void =
    E := subscribable_event(int){}
    R := relay{E := E}
    S1 := E.Subscribe(R.On)
    E.Signal(1)
    E.Signal(2)
    S1.Cancel()
    S1.Cancel()
    E.Signal(3)
    E2 := subscribable_event(int){}
    if (S := E2.Subscribe(Late), 1 > 2) then Print("no") else Print("rolled back")
    E2.Signal(4)
    P := subscribable_event(tuple(int, string)){}
    PS := P.Subscribe(ShowPt)
    P.Signal((7, "x"))
    if (PS.Cancel(), 1 > 2) then Print("no") else Print("cancel rolled back")
    P.Signal((8, "y"))
    PS.Cancel()
    P.Signal((9, "z"))
    C := ctr{}
    E3 := subscribable_event(int){}
    for (I := 0..3000):
        CS := E3.Subscribe(C.On)
        E3.Signal(1)
        CS.Cancel()
    Print("n {C.N}")
