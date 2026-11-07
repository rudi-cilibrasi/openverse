# expect: return is not allowed in a constructor
p := class:
    A:int = 0
MkP<constructor>() := p:
    A := block:
        return
        1
Main():void = Print("x")
