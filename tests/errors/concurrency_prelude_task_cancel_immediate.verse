# expect: Cancel suspends: it can only be called in a <suspends> function
Bad(T:task(int)):void=T.Cancel()
Main():void=Print("ok")
