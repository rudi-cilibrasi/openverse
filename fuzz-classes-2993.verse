# uninhabited: i7
i1 := interface:
    F2:int = 19
    S3:string = "blue"
    M4(?Nm5:int = 8):int
    M6()<computes>:int
i7 := interface:
    var F8:int = 13
    S9:string = ""
    M10()<writes>:int =
        set F8 = 6 * 1
        S9.Length + S9.Length + S9.Length
    M11(P12:int)<reads>:string
    M13(P14:int, P15:int)<transacts>:i7 =
        set F8 = P15 + 7
        Self
i16 := interface:
    F17:int = 10
    M18(P19:i1):int =
        L1 := P19.(i1:)M6()
        2
    M6()<computes>:int
c20 := class<abstract>:
    S21:string = ""
    var F22:int = 4
    S23:string = "ok"
    M24(P25:int):int =
        5 + F22
c26 := class<abstract>(c20):
    S27:string = "ok"
    S23<override>:string = "red"
    M24<override>(P25:int):int = 2
    M28(P29:int)<transacts>:c26
    M30()<reads>:string =
        "{S23}"
c31 := class(c26, i1):
    S32:string = "n"
    var O33:?i7 = false
    S3<override>:string = "ok"
    M4<override>(?Nm5:int = 3)<writes>:int =
        L2 := F2 + Nm5 + 5
        set F22 = S27.Length + F2
        8 + 0 + 0
    M24<override>(P25:int):int = (if (F2 <> F2) then F22 * 1 else F22)
    M28<override><final>(P29:int)<reads><writes>:c31 = Self
    M6<override>()<computes>:int =
        F2 + F2 - F2
    block:
        defer:
            Print("block defer c31")
        Print("block c31 {S3}{S32}{S3}")
c34 := class<abstract>(c20, i16):
    S35:string = ""
    S36:string = "n"
    M24<override>(P25:int):int =
        L3 := Max(Min(S35.Length, S35.Length), P25)
        3 - P25
c37 := class(c34, i1):
    var B38:c31 = c31{}
    var F22<override>:int = 7
    F17<override>:int = 4
    (i1:)M6<override>()<computes>:int = (if (1 = F17) then F2 else 2 + F17)
    M39(P40:int)<reads>:c37 = Self
    M4<override>(?Nm5:int = F17 + 9):int =
        set F22 += F2
        S36.Length + F2 + F22
    (i16:)M6<override>()<computes>:int =
        if (S35.Length > 4):
            return S3.Length - S35.Length
        F2
Mkc37_41<constructor>(Arg43:string, ?Opt42:int = 6) := c37:
    B38 := c31{}
Total44(Xs:[]c26):int =
    var N:int = 0
    for (X : Xs) { set N += X.M24(9) }
    N
Total45(Xs:[]c20):int =
    var N:int = 0
    for (X : Xs) { set N += X.M24(N) }
    N
Main():void =
    O4 := c31{F22 := 9 - 0}
    O5 := c31{S32 := "a", S21 := "", S3 := ":{8}"}
    O6 := c37{F22 := 9 + 8, F17 := Min(2, 3)}
    set O6.B38 = O4
    set O6.B38.F22 += 8
    Print("c37: {O6.S21} {O6.F22} {O6.F17} {O6.S35} {O6.S36} {O6.M18(O6)} {O6.M4()} {O6.(i1:)M6()} {O6.M39(5 + 6).M18(O5)}")
    Print("c31: {O4.S21} {O4.S23} {O4.F2} {O4.S32} {O4.M24(8 + 5)} {O4.M28(8 * 3).M24(9)} {O4.M30()} {O4.M4(?Nm5 := 6 + 5)} {O4.M6()}")
    if (set O4.O33?.F8 += 7, Z7 := O4.O33?) then Print("through {Z7.F8}") else Print("empty O33")
    Print("c31: {O5.F22} {O5.S23} {O5.S3} {O5.S32} {O5.M24(5)} {O5.M30()} {O5.M4(?Nm5 := 4 * 2)} {O5.(i1:)M6()}")
    set O5.F22 += 2
    Al8 := O5
    set Al8.F22 += 4
    Print("O5.F22 = {O5.F22}")
    if (set O5.O33?.F8 += 2, Z9 := O5.O33?) then Print("through {Z9.F8}") else Print("empty O33")
    Xs10:[]c26 = array{O5, O4}
    for (X11 : Xs10):
        defer:
            Print("after {X11.M24(1)}")
        Print("c26 {X11.M24(1)} {X11.M28(8).M24(6)} {X11.M30()} {X11.S21} {X11.F22}")
        set X11.F22 += 2
    for (X12 : Xs10, Y13 := c31[X12]) { Print("as c31 {Y13.M6()}") }
    Print("total {Total44(Xs10)}")
    Xs14:[]i1 = array{O5, O4, O6}
    for (I16 -> X15 : Xs14) { Print("i1 {I16} {X15.(i1:)M6()}") }
    for (X17 : Xs14, Y18 := c37[X17]) { Print("as c37 {Y18.(i16:)M6()}") }
    var Cur19:i1 = O5
    for (X20 : Xs14, X20.M4(?Nm5 := 8) > 2) { set Cur19 = X20 }
    Print("cur {Cur19.M6()}")
    Xs21:[]c20 = array{O6, O4, O5}
    for (I23 -> X22 : Xs21) { Print("c20 {I23} {X22.M24(5)} {X22.S21} {X22.F22}") }
    for (X24 : Xs21, Y25 := c37[X24]) { Print("as c37 {Y25.(i16:)M6()}") }
    Print("total {Total45(Xs21)}")
    Xs26:[]c31 = array{O4, O5}
    for (I28 -> X27 : Xs26) { Print("c31 {I28} {X27.M24(1)} {X27.M28(9).M24(6)} {X27.M30()} {X27.M4()} {X27.(i1:)M6()} {X27.F22} {X27.S23} {X27.S3}") }
    U29 := c31(O4)
    Print("up {U29.M6()}")
    var Kept30:[]c20 = array{}
    var Acc31:int = 0
    for (I32 := 1..50):
        V33 := Mkc37_41("{I32}")
        set V33.F22 += I32
        if (Mod[I32, 13] = 0) then set Kept30 = Kept30 + array{V33}
        if (set V33.F22 = 1000, set Kept30 = Kept30 + array{V33}, I32 > 47) then set Acc31 += 1
        if (R := Mod[V33.M4(?Nm5 := I32), 1000]) then set Acc31 += R
    Print("stress {Acc31} {Kept30.Length}")
    for (X34 : Kept30, Mod[Kept30.Length, 2] = 0) { Print("kept {X34.M24(1)}") }
    Print("again {O6.M24(O6.M4(?Nm5 := 2))}")
    Print("again {O4.(i1:)M6()}")
    Print("again {O5.M4(?Nm5 := 2)}")
