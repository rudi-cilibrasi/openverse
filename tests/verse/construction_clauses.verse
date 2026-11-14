# A construction's let: and block clauses (Book of Verse ch. 10, "Let
# Clauses in Archetypes"): let: definitions are visible to the field
# initializers after them, a block runs where it is written, and the
# fields and clauses run in the order they are written.
rect := class:
    Width:int
    Height:int
    Area:int
counter := struct:
    A:int
    B:int = 9
Square(N:int):rect = rect:
    let:
        S:int = N
    Width := S
    Height := S
    Area := S * S
Main():void =
    var Y:int = 0
    Sq := Square(4)
    R := rect:
        block:
            set Y = 2
        let:
            W := Y + 1
        Width := W
        Height := Y
        Area := W * Y
    C := counter{A := Y, block{set Y = 5}, B := Y}
    D := counter{block{set Y += 1}, A := Y}
    Print("{Sq.Area} {R.Width} {R.Height} {R.Area} {C.A} {C.B} {D.A} {D.B} {Y}")
