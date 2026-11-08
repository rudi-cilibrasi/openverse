# expect: 2:30: a choice (a | b) has several values, so it must be in a failure context that takes them
F(X:int)<decides>:int = X = 1 | 2
Main():void = Print("x")
