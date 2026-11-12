On():void=Print("got")
Main():void=
    E:=subscribable_event(){}
    S:=E.Subscribe(On)
    E.Signal()
    S.Cancel()
    E.Signal()
    Print("ok")
