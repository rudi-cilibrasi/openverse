# expect: a constructor's body has field initializers
p := class:
    A:int = 0
MkP<constructor>() := p:
    A := 1
    {Print("x")}
Main():void = Print("x")
