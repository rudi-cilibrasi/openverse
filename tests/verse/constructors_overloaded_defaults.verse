# an overload that leaves a field to another overload gives it its default,
# evaluated outside the constructor (a parameter named like a global does
# not capture it), and a delegation cycle through overloads that ends

Lim:int = 5
p := class:
    A:int = Lim
    B:int = 0
K<constructor>(Given:int) := p:
    B := Given
K<constructor>(S:string) := p:
    A := 2
Main():void =
    V := K(9)
    Print("{V.A} {V.B}")
