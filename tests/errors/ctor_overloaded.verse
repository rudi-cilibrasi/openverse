# expect: the overloads of constructor MkP construct p and q: they must construct one class
p := class:
    A:int = 0
q := class:
    A:int = 0
MkP<constructor>() := p:
    A := 1
MkP<constructor>(X:int) := q:
    A := X
Main():void = Print("x")
