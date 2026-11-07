# expect: constructor MkP is defined twice (overloaded constructors are not supported yet)
p := class:
    A:int = 0
MkP<constructor>() := p:
    A := 1
MkP<constructor>(X:int) := p:
    A := X
Main():void = Print("x")
