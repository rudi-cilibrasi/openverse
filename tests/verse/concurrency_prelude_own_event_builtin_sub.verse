event(t:type):=class{N:int=7}
On(X:int):void=Print("got {X}")
Main():void=
    E:=subscribable_event(int){}
    S:=E.Subscribe(On)
    E.Signal(event(int){}.N)
    S.Cancel()
    E.Signal(8)
