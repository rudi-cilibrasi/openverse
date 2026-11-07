# overloaded <computes> constructors that fill in defaults (#80 review)
p := class:
    A:int = 1
    B:int = 0
K<constructor>(X:int)<computes> := p:
    B := X
K<constructor>(S:string)<computes> := p:
    A := 2
Mk(X:int)<computes>:p = K(X)
Main():void =
    V := Mk(9)
    Print("{V.A} {V.B}")
