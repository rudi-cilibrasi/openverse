# expect: K<constructor> is defined twice with parameters a call cannot tell apart, (int) and (int)
p := class:
    A:int
    B:int = 0
q := class:
    A:int = 0
K<constructor>(X:int) := p:
    A := X
K<constructor>(Y:int) := p:
    A := Y
Main():void = Print("x")
