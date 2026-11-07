# uninhabited: i2
Helper1(X:int):int = X * 3 + 2
i2 := interface:
    S3:string
    var F4:int = Helper1(0)
    M5(?Nm6:int = 9)<reads>:i2
    M7(P8:int)<computes>:int
    M9(P10:int, P11:int, ?Nm12:int = 2)<reads>:string
i13 := interface:
    var O14:?i2 = false
    M15(P16:int):int
    M17(P18:int, P19:i2)<reads>:int = P18 + P18 - 5
    M20():int =
        defer:
            Print("defer M20")
        (i13:)M7(1)
    M7(P8:int)<computes>:int = P8
c21 := class<unique>:
    F22:int = 10
    M23()<reads><allocates>:c21 = Self
    block:
        Print("block c21 q{9}q")
c24 := class(c21):
    M23<override>()<reads><allocates>:c24 = Self
c25 := class(c24):
    S26:string = "n"
    D27(P28:int)<decides><reads>:int =
        P28 <> F22
        P28 - P28
c29 := class(c24, i13):
    S30:string = "n"
    M23<override>()<reads><allocates>:c29 =
        defer:
            Print("defer M23")
        Self
    M17<override>(P18:int, P19:i2)<computes>:int =
        P19.(i2:)M7(P19.M7(F22))
    M20<override>():int =
        (super:)M20() + 7 * 3
    M15<override>(P16:int)<transacts>:int =
        defer:
            Print("defer M15")
        (if (F22 < S30.Length) then Max(S30.Length, 2) else Max(P16, 7))
c31 := class(c21):
    var F32:int = 7
    var F33:int = 5
    F34:int = Helper1(4)
c35 := class(c31, i13):
    B36:c25 = c25{}
    B37:c29 = c29{}
    var F38:int = 5
    M7<override>(P8:int)<computes>:int =
        L1 := F22
        6 + 7 + F34 + (super:)M7(7)
    M41(P42:int):string =
        "x"
    D39(P40:int)<reads><decides>:int =
        P40 < 6
        Max((if (B36.D27[F34]) then 3 else 0), F34)
    M15<override><final>(P16:int):int =
        9 + F32 - F38
    block:
        Print("block c35 q{1}")
c43 := class(c31):
    S44:string = "red"
    F22<override>:int = 15
    M46()<reads>:int =
        L2 := F22 - F32 + F34 * 1
        if (9 > F33):
            return F34 * 1
        F34 + Min(L2, 7)
    M45<final>():string =
        set F33 += 1
        "a{Max(3, 5)}"
Mkc35_47<constructor>(Arg48:string) := c35:
    let:
        K3 := Arg48.Length - Arg48.Length
    F38 := K3 * 2 - K3
    F34 := Min(K3 + Arg48.Length, Arg48.Length)
Mkc35_47<constructor>(Arg49:string, Arg50:int) := c35:
    let:
        K4 := 5 + Arg50
    block:
        defer:
            Print("ctor defer Mkc35_47")
        Print("ctor c35 {Arg49}")
    F33 := K4
Mkc43_51<constructor>(Arg52:int, Arg53:string) := c43:
    F32 := 7 + 1 - 8
Show54(X:int):string = "int {X}"
Show54(X:string):string = "str {X}"
Show54(X:c21):string = "c21 {X.M23().F22}"
Show54(X:c21, Y:int):string = "c21 and {Y}"
Total55(Xs:[]c43):int =
    var N:int = 0
    for (X : Xs) { set N += X.M46() }
    N
Main():void =
    O5 := c21{}
    O6 := c24{}
    O7 := c25{S26 := "x"}
    O8 := c29{}
    O9 := c29{}
    O10 := c31{F32 := (if (9 < 6) then 3 else 1)}
    O11 := Mkc35_47("q-", 2)
    O12 := c43{F32 := 6 - 9}
    O13 := Mkc43_51(5 * 1, "q")
    Print("c29: {O9.S30} {O9.M23().F22} {O9.M15(0 + 8)}")
    if (set O9.O14?.F4 += 9, Z14 := O9.O14?) then Print("through {Z14.F4}") else Print("empty O14")
    Print("c43: {O12.F34} {O12.M23().F22} {O12.M45()}")
    set O12.F33 += 2
    Al15 := O12
    set Al15.F33 += 1
    Print("O12.F33 = {O12.F33}")
    Print("c43: {O13.F34} {O13.S44} {O13.M23().F22} {O13.M46()}")
    set O13.F33 -= 4
    Al16 := O13
    set Al16.F33 += 4
    Print("O13.F33 = {O13.F33}")
    Print("c29: {O8.F22} {O8.S30} {O8.M23().F22} {O8.M15(4 - 7)} {O8.M7(9 - 1)} {O8.(i13:)M7(4 + 3)}")
    Print("c24: {O6.F22}")
    Print("c31: {O10.F33} {O10.F34} {O10.M23().F22}")
    set O10.F32 *= 2
    Al17 := O10
    set Al17.F32 += 1
    if (set O10.F32 = 6, O10.F32 > 13) then Print("kept {O10.F32}") else Print("rolled back {O10.F32}")
    Print("O10.F32 = {O10.F32}")
    Print("c25: {O7.F22} {O7.S26}")
    Print("c21: {O5.F22}")
    Print("c35: {O11.F22} {O11.F33} {O11.F34} {O11.F38} {O11.M23().F22} {O11.(i13:)M7(9 - 1)} {O11.M41(5 * 1)}")
    if (W18 := O11.D39[4]) then Print("D39 yes {W18}") else Print("D39 no")
    set O11.F32 = 2
    if (set O11.F32 = 14, O11.F32 > 13) then Print("kept {O11.F32}") else Print("rolled back {O11.F32}")
    Print("O11.F32 = {O11.F32}")
    if (set O11.O14?.F4 += 1, Z19 := O11.O14?) then Print("through {Z19.F4}") else Print("empty O14")
    if (O10 = O6) then Print("eq") else Print("ne")
    if (O10 <> O10) then Print("ne") else Print("eq")
    Xs20:[]c21 = array{O8, O9, O7, O6, O10, O13, O5, O12, O11}
    for (X21 : Xs20):
        defer:
            Print("after {X21.M23().F22}")
        Print("c21 {X21.M23().F22}")
    for (X22 : Xs20, Y23 := c25[X22]) { Print("as c25 {Y23.M23().F22}") }
    Xs26:[]c31 = array{O11, O13, O10, O12}
    for (I28 -> X27 : Xs26) { Print("c31 {I28} {X27.M23().F22} {X27.F32} {X27.F33}") }
    if (set Xs26[1].F32 *= 2, Y29 := Xs26[0]) then Print("path {Y29.F32}") else Print("no path")
    for (X30 : Xs26):
        if (Y31 := c35[X30]) then Print("is c35 {Y31.M41(5)}") else Print("not c35")
    U34 := c31(O11)
    Print("up {U34.M23().F22}")
    Xs35:[]i13 = array{O11, O9, O8}
    for (X36 : Xs35):
        defer:
            Print("after {X36.M15(7)}")
        Print("i13 {X36.M15(7)} {X36.M20()} {X36.M7(7)} {X36.(i13:)M7(9)}")
    for (X37 : Xs35):
        if (Y38 := c35[X37]) then Print("is c35 {Y38.(i13:)M7(4)}") else Print("not c35")
    Xs39:[]c43 = array{O12, O13}
    for (I41 -> X40 : Xs39) { Print("c43 {I41} {X40.M23().F22} {X40.M46()} {X40.F32} {X40.F33} {X40.F34}") }
    Print("total {Total55(Xs39)}")
    Print("again {O9.M7(8)}")
    Print("again {O12.M23().F22}")
    Print("again {O13.M45()}")
    Print(Show54(c21{}, 7))
    Print(Show54(0))
    Print(Show54("b"))
    Print(Show54(Show54(5)))
    Print(Show54(c24{}))
    Print(Show54(c35{F34 := Min(9, 6)}))
    Print(Show54(Mkc43_51(0 + 9, "-{5}{0}")))
