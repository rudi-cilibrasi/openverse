# expect: K<constructor> calls the default of A, which has the effect
G()<transacts>:int = 1
p := class:
    A:int = G()
    B:int = 0
K<constructor>(X:int)<computes> := p:
    B := X
K<constructor>(S:string)<computes> := p:
    A := 2
Main():void = Print("{K(1).A}")
