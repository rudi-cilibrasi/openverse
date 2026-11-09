# choices whose alternatives have several values, where the first success is taken: in an if, with names bound after, in option{…} (#283)
A():int = 1 | 2
B():int = 10 | 20
C():int = A() | B()
Upto(Lo:int, Hi:int)<computes><decides>:int =
    Lo <= Hi
    Lo | Upto[Lo + 1, Hi]
Main():void =
    if (X := C(), X > 5) then Print("c {X}")
    if (X := A() | 5, X > 2) then Print("a {X}")
    if (X := Upto[1, 3] | 9, X > 2, Y := X * 2) then Print("u {X} {Y}")
    if (O := option{X := A() | B(); X > 15; X}, V := O?) then Print("o {V}")
