# expect: A is defined twice with parameters a call cannot tell apart, (?Y:int, ?X:int) and (?X:int, ?Y:int)
A(?Y:int, ?X:int):int = 0
A(?X:int, ?Y:int):int = 1
Main():void = Print("x")
