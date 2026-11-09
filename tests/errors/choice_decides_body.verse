# expect: 3:25: a choice (a | b) has several values, so it must be in a failure context that takes them
c := class:
    M()<decides>:int = 1 | 2
Main():void = Print("x")
