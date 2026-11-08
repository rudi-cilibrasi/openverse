# expect: Get suspends: it can only be called in a <suspends> function
Get()<suspends>:int = 1
Main():void = Print("{Get()}")
