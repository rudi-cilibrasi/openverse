event(t:type):=class:
    N:int=7
    Signal(X:t):void=Print("user {N}")
Main()<suspends>:void=event(int){}.Signal(1)
