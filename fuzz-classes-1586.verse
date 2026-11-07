# uninhabited: i2
Helper1(X:int):int = X * 1 + 1
i2 := interface:
    var O3:?i2 = false
    var F4:int = 0
    M5(P6:int):int
    M7(P8:int)<computes>:int = 5 + 1 + P8
    M9(P10:int)<reads>:int
c11 := class:
    var F12:int = 12
    var F13:int = Helper1(6)
    F14:int = 16
    M5(P6:int):int =
        L1 := F13 + F14 + 6 + F12
        Max(P6, 5) + (if (3 <> 5) then 2 else 5)
c15 := class(c11):
    var O16:?i2 = false
    S17:string = "red"
    F18:int = 7
    M21(P22:c11)<computes>:c15 =
        defer:
            Print("defer M21")
        Self
    M19(P20:int):int =
        L2 := (c11:)M5(F13) + P20
        defer:
            set F13 += 2
        set F13 -= F14
        (c11:)M5(S17.Length)
Total23(Xs:[]c11):int =
    var N:int = 0
    for (X : Xs) { set N += X.M5(N) }
    N
Main():void =
    defer:
        Print("main done")
    O3 := c11{F13 := 3 + 6, F14 := Min(0, 0)}
    O4 := c15{F13 := Max(4, 3), F18 := 6 + 9, S17 := "{2}"}
    Print("c15: {O4.F12} {O4.F13} {O4.(c11:)M5(0 - 9)} {O4.M19(9)}")
    set O4.F13 *= 3
    Al5 := O4
    set Al5.F13 += 2
    if (set O4.F13 = 20, O4.F13 > 13) then Print("kept {O4.F13}") else Print("rolled back {O4.F13}")
    Print("O4.F13 = {O4.F13}")
    if (set O4.O16?.F4 += 8, Z6 := O4.O16?) then Print("through {Z6.F4}") else Print("empty O16")
    Print("c11: {O3.F12} {O3.F13} {O3.F14} {O3.M5(9 + 6)} {O3.(c11:)M5((if (5 > 9) then 1 else 4))}")
    set O3.F12 += 2
    Print("O3.F12 = {O3.F12}")
    Xs7:[]c11 = array{O4, O3}
    for (I9 -> X8 : Xs7) { Print("c11 {I9} {X8.M5(3)} {X8.(c11:)M5(3)} {X8.F14}") }
    if (set Xs7[2].F12 *= 3, Y10 := Xs7[0]) then Print("path {Y10.F12}") else Print("no path")
    for (X11 : Xs7, Y12 := c15[X11]) { Print("as c15 {Y12.(c11:)M5(0)}") }
    Print("total {Total23(Xs7)}")
    var Cur13:c11 = O4
    for (X14 : Xs7, X14.M5(6) > 20) { set Cur13 = X14 }
    Print("cur {Cur13.M5(0)}")
    U15 := c11(O4)
    Print("up {U15.M5(8)}")
    Print("again {O4.M19(Max(7, 0))}")
    Print("again {O3.M5(4)}")
