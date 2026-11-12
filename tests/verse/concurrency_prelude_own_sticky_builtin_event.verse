sticky_event(t:type):=class:
    Signal(X:t):void=Print("user sticky")
Main():void=
    E:=event(int){}
    E.Signal(3)
    sticky_event(int){}.Signal(7)
