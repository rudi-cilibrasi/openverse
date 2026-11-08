# expect: Cancel suspends: it can only be called in a <suspends> function
W()<suspends>:int = 1
F(T:task(int)):void = T.Cancel()
Main():void = Print("x")
