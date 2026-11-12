subscribable_event(t:type):=class:
    Signal(X:t):void=Print("user sub")
Main():void=subscribable_event(int){}.Signal(1)
