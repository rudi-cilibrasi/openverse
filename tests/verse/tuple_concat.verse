base := class<computes> { N:int }
left := class<computes>(base) {}
right := class<computes>(base) {}

Main():void =
    X := (1, 2)
    Y := (3, 4)
    A := X + Y
    if (A = array{1, 2, 3, 4}) then Print("pairs")
    B := (0, 1) + array{2, 3} + (4, 5)
    if (B = array{0, 1, 2, 3, 4, 5}) then Print("mixed operands")
    Text := ('a', 'b') + ('c', 'd')
    Print(Text)
    Objects := (left{N:=1}, right{N:=2}) + (right{N:=3}, left{N:=4})
    for (Object : Objects) { Print("object {Object.N}") }
    Mixed := (1, "two") + (3.0, true)
    Print("mixed elements {Mixed.Length}")
    Nested := ((1, 2), (3, 4)) + array{(5, 6)}
    if (Last := Nested[2]) then Print("nested {Last(0)} {Last(1)}")
    Empty:true = false
    FromTrue := Empty + A
    FromVoid := () + A + ()
    Print("empty {FromTrue.Length} {FromVoid.Length}")
