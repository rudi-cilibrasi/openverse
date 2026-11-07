# expect: B is defined twice with parameters a call cannot tell apart
B(?X:int = 42):int = 0
B(?X:int):int = 1
Main():void = Print("x")
