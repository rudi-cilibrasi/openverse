# A range bound of a for clause that fails gives no iterations, as a failing
# source does (Book of Verse ch. 7: "When any expression in the iteration
# header fails, that iteration is skipped"); what either bound did is rolled
# back. The for itself does not fail, so it needs no failure context.
counter := class:
    var V:int = 0
    Bump(Stop:int)<decides><transacts>:int =
        set V = V + 1
        V <> Stop
        V

Main():void =
    A := counter{}
    Lo := for (I := 1..A.Bump[1]) { I }
    Print("upper fails: {Lo.Length} {A.V}")
    B := counter{}
    Hi := for (I := B.Bump[5]..B.Bump[2]) { I }
    Print("lower then upper: {Hi.Length} {B.V}")
    C := counter{}
    Both := for (I := C.Bump[5]..C.Bump[5]) { I }
    Print("both succeed: {Both.Length} {C.V}")
    # (an inner generator's bound, for each outer element)
    D := counter{}
    Inner := for (J := 1..3, I := 1..D.Bump[2]) { 10 * J + I }
    for (X : Inner) { Print("inner {X}") }
    Print("inner bumps: {D.V}")
