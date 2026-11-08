# expect: a <suspends> constructor is not supported
entity := class:
    N:int
MakeE<constructor>(X:int)<suspends> := entity:
    N := X
Main():void = Print("x")
