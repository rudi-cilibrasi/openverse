# expect: MkD sets B after delegating to MkB: set the fields of d first, then delegate
p := class:
    A:int = 0
b := class:
    X:int
d := class(b):
    B:int
MkB<constructor>(V:int) := b:
    X := V
MkD<constructor>(V:int) := d:
    MkB<constructor>(V)
    B := V
Main():void = Print("x")
