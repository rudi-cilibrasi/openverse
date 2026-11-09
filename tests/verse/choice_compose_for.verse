# the same in fors: after another generator and before a filter, before a choice, with an alternative that prints (#283)
A():int = 1 | 2
B():int = 10 | 20
C():int = A() | B()
Upto(Lo:int, Hi:int)<computes><decides>:int =
    Lo <= Hi
    Lo | Upto[Lo + 1, Hi]
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
Main():void =
    R := for (X := C()) { X }
    Print("{R.Length}")
    for (Y := 0 | 1, X := A() | Y + 5, X <> 2) { Print("{Y} {X}") }
    for (X := Upto[1, 2] | 9, Z := 0 | 1) { Print("u {X} {Z}") }
    for (X := Tell("t", 1) | B()) { Print("e {X}") }
