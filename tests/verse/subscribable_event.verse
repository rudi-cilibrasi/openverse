# subscribable_event (#210): functions and methods subscribed, signalled and
# cancelled; events as fields with their own defaults; a handler that
# cancels its own subscription; generic code that signals
button := class:
    Pressed:subscribable_event(int) = subscribable_event(int){}
    Press(N:int):void = Pressed.Signal(N)
door := class:
    var Opens:int = 0
    B:button
    var Sub:?cancelable = false
    Attach():void =
        set Sub = option{B.Pressed.Subscribe(OnPress)}
    OnPress(N:int):void =
        set Opens += N
        if (N > 5, S := Sub?) then S.Cancel()
Fire(E:subscribable_event(t), V:t where t:type):void = E.Signal(V)
Late(N:int):void = Print("late {N}")
Main():void =
    B1 := button{}
    B2 := button{}
    D := door{B := B1}
    D.Attach()
    B1.Press(2)
    B2.Press(100)
    Fire(B1.Pressed, 7)
    B1.Press(1)
    Print("opens {D.Opens}")
    E := subscribable_event(string){}
    X := E.Subscribe(Late2)
    Fire(E, "a")
    Fire(E, "b")
    Board()
Late2(S:string):void = Print("got {S}")
scoreboard := class:
    var Total:int = 0
    OnScore(P:int):void =
        set Total += P
LogIt(P:int):void = Print("scored {P}")
Board():void =
    E := subscribable_event(int){}
    B := scoreboard{}
    C1 := E.Subscribe(LogIt)
    C2 := E.Subscribe(B.OnScore)
    E.Signal(3)
    E.Signal(4)
    C1.Cancel()
    E.Signal(5)
    Print("total {B.Total}")
