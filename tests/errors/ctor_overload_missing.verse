# expect: K does not set A, a field of p without a default
p := class:
    A:int
    B:int = 0
q := class:
    A:int = 0
K<constructor>(X:int) := p:
    A := X
K<constructor>(S:string) := p:
    B := 1
Main():void = Print("x")
