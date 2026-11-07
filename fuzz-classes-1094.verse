# uninhabited: i1 i7 i13
i1 := interface:
    var F2:int = 15
    M3(P4:int, P5:int)<computes>:string
    M6()<reads>:string
i7 := interface:
    M8(?Nm9:int = 1):int
    M10()<transacts>:int = 7
    M11(P12:int):int =
        L1 := 9
        Min(M3(L1, 9).Length, 9)
    M3(P4:int, P5:int)<computes>:string
i13 := interface:
    M14(P15:int):int
    M16(P17:int)<reads>:int
    M18(P19:int):int
c20 := class<abstract>:
    var O21:?i1 = false
    var F22:int = 18
    M23(?Nm24:int = 9)<reads><writes>:int
    M25(P26:int)<computes>:string =
        defer:
            Print("defer M25")
        "x"
    block:
        defer:
            Print("block defer c20")
        set F22 += (if (0 <> 0) then F22 else F22)
        Print("block c20 :{5}")
c27 := class(c20):
    F28:int = 10
    var O29:?i13 = false
    var F30:int = 7
    M23<override>(?Nm24:int = F28)<reads><writes>:int =
        defer:
            Print("defer M23")
        L2 := (if (N3 := O21?) then N3.F2 else 6)
        set F22 = 3 - F28
        1 - 7
    M25<override>(P26:int)<computes>:string = "+{(super:)M25(F28)}"
    M31(P32:int, ?Nm33:int = P32 + P32)<writes>:int = 9
Mkc27_34<constructor>(Arg35:int, Arg36:int) := c27:
    F28 := Min(Arg35, Arg36) + 3
    F22 := Min(4, Arg35) + 2
Mkc27_34<constructor>(Arg37:string) := c27:
    block:
        Print("ctor c27 {Arg37.Length}{Arg37.Length}{Arg37}")
    Mkc27_34<constructor>(Arg37.Length, Arg37.Length * 1)
Main():void =
    O4 := c27{}
    Print("c27: {O4.F28} {O4.M31(7 * 3, ?Nm33 := 3 * 2)}")
    set O4.F30 *= 1
    Al5 := O4
    set Al5.F30 += 1
    if (set O4.F30 = 19, O4.F30 > 6) then Print("kept {O4.F30}") else Print("rolled back {O4.F30}")
    Print("O4.F30 = {O4.F30}")
    if (set O4.O21?.F2 += 7, Z6 := O4.O21?) then Print("through {Z6.F2}") else Print("empty O21")
    Print("again {O4.M31(3 * 1)}")
