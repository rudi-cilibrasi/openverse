# expect: expected string, found int (in a call of K)
box(t:type) := class:
    Value:t
plain := class:
    N:int = 0
K<constructor>(V:t where t:type) := box(t):
    Value := V
Use():void =
    B:box(string) = K(1)
Main():void = Print("x")
