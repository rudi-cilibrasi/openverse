On(X:int):void=Print("got {X}")
Main():void=
    E:=subscribable_event(int){}
    S:=E.Subscribe(On)
    E.Signal(7)
    S.Cancel()
    E.Signal(8)
    Print("ok")
