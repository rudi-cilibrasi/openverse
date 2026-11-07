# constructor functions (#72 review): an abstract class's constructor,
# delegated to; initializers at the field's type (false, array{}, map{});
# one-line and braced bodies

e := class<abstract>:
    N:int
    F():int
d := class(e):
    F<override>():int = N * 2
MkE<constructor>(X:int) := e:
    N := X
MkD<constructor>(X:int) := d:
    MkE<constructor>(X)

p := class:
    A:?int
    B:[]int
    C:[string]int
MkP<constructor>() := p:
    A := false
    B := array{}
    C := map{}

q := class:
    V:int
    W:int = 0
MkQ<constructor>(X:int) := q: V := X; W := X + 1
MkR<constructor>(X:int) := q{V := X}

Main():void =
    Print("{MkD(4).F()}")
    P := MkP()
    if (X := P.A?) then Print("{X}") else Print("none {P.B.Length} {P.C.Length}")
    Print("{MkQ(1).V} {MkQ(1).W} {MkR(5).V} {MkR(5).W}")
