# expect: the default of A calls G
G()<transacts>:int = 1
p := class:
    A:int = G()
    B:int = 0
K<constructor>(X:int)<computes> := p:
    B := X
K<constructor>(S:string)<computes> := p:
    A := 2
Main():void = Print("{K(1).A}")
