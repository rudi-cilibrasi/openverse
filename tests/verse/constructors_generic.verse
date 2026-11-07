# constructor functions of parametric classes, and generic ones: the
# archetype names the class's type arguments, := box(t):, which may mention
# the constructor's own type parameters (where t:type)

box(t:type) := class:
    Value:t
    Count:int = 0
    Get():t = Value

pair(a:type, b:type) := class:
    First:a
    Second:b

intbox := class(box(int)):
    Label:string = ""

MakeBox<constructor>(V:t where t:type) := box(t):
    Value := V
    Count := 1

MakeIntBox<constructor>(V:int) := box(int):
    Value := V * 2

MakePair<constructor>(X:a, Y:b where a:type, b:type) := pair(a, b):
    First := X
    Second := Y

MakeSwapped<constructor>(X:a, Y:b where a:type, b:type) := pair(b, a):
    First := Y
    Second := X

MakeLabeled<constructor>(V:int, L:string) := intbox:
    Label := L
    MakeBox<constructor>(V)

MakeOpt<constructor>(V:t where t:type) := box(?t):
    Value := option{V}

Main():void =
    B := MakeBox(5)
    S := MakeBox("hi")
    Print("{B.Get()} {B.Count} {S.Get()}")
    Print("{MakeIntBox(4).Get()}")
    P := MakePair(1, "one")
    Q := MakeSwapped(1, "one")
    Print("{P.First} {P.Second} {Q.First} {Q.Second}")
    L := MakeLabeled(7, "seven")
    Print("{L.Get()} {L.Count} {L.Label}")
    if (V := MakeOpt(9).Get()?) then Print("{V}")
