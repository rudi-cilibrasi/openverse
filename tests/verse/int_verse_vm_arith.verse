# Ints are the Verse VM's (#724): arithmetic past the signed 64-bit range
# gives the exact result. Epic's Verse VM (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM", 2026-11-18) prints
# the first five lines (the probes int-overflow, book-int-mul-overflow,
# book-int-negate-min, book-int-abs-min, book-int-floor-div-min,
# book-int-sub-below-min and book-int-compound-add in
# tests/conformance/versevm); its Blueprint VM stops at the first with
# "integer add overflow". The values are printed by Show, 18 digits at a
# time, as ToString refuses an int beyond 64 bits.
Digits18(X:int):string =
    var S:string = "{X}"
    loop:
        if (S.Length >= 18) then break
        set S = "0" + S
    S

Show(X:int):string =
    if (X >= -9223372036854775807, X <= 9223372036854775807) then "{X}"
    else if (X < 0) then "-" + Show(-X)
    else if (Q := Quotient[X, 1000000000000000000], R := Mod[X, 1000000000000000000]) then Show(Q) + Digits18(R)
    else "?"

Next(N:int)<computes>:int = N + 1
Times(A:int, B:int)<computes>:int = A * B
FloorQuotient(A:int, B:int)<computes><decides>:int = Floor(A / B)

Main():void =
    Top:int = 9223372036854775807
    Bottom:int = -9223372036854775807 - 1
    if (Next(Top) > Top) then Print("add: above signed 64-bit max")
    if (Times(Bottom, -1) > Top) then Print("mul: above signed 64-bit max")
    if (-Bottom > Top, Abs(Bottom) > Top) then Print("negate, abs: above signed 64-bit max")
    if (Q := FloorQuotient[Bottom, -1], Q > Top) then Print("floor division: above signed 64-bit max")
    if (Bottom - 1 < Bottom) then Print("sub: below signed 64-bit min")
    var X:int = Top
    set X += 1
    Print("set += {Show(X)}")
    set X *= X
    Print("set *= {Show(X)}")
    set X -= 1
    Print("set -= {Show(X)}")
    Print("add {Show(Top + 1)} sub {Show(Bottom - 1)}")
    Print("mul {Show(Top * Top)} {Show(Bottom * Bottom)} {Show(Bottom * Top)}")
    Print("neg {Show(-Bottom)} abs {Show(Abs(Bottom))} {Show(Abs(Bottom * 3))}")
    # back in 64 bits: an ordinary int again
    if (Y := (Top + 1) - 1, Y = Top) then Print("back {Y}")
    if (Y := (Bottom * Bottom) / (Bottom * Bottom), Floor(Y) = 1) then Print("back {Floor(Y)}")
    # the divisions, past 64 bits on either side
    Big:int = Top * Top * 7 + 5
    if (Q := Quotient[Big, Top]) then Print("quotient {Show(Q)}")
    if (R := Mod[Big, Top]) then Print("mod {Show(R)}")
    if (Q := Quotient[-Big, Top], R := Mod[-Big, Top]) then Print("negative {Show(Q)} {Show(R)}")
    if (Q := Quotient[Big, -Top], R := Mod[Big, -Top]) then Print("negative divisor {Show(Q)} {Show(R)}")
    if (F := Floor(-Big / Top), C := Ceil(-Big / Top)) then Print("floor {Show(F)} ceil {Show(C)}")
    if (Q := Quotient[Big, Big * Big]) then Print("small quotient {Q}")
    if (not Quotient[Big, 0], not Mod[Big, 0], not Floor(Big / 0)) then Print("a zero divisor fails")
    # comparisons and equality
    if (Big = Top * Top * 7 + 5, Big <> Big + 1, Big < Big + 1, -Big < Bottom, Big >= Big) then Print("compare")
    if (Top + 1 <> Top, Bottom - 1 <> Bottom, Top + 1 = -(Bottom)) then Print("distinct from 64-bit ints")
    if (Min(Big, Top) = Top, Max(-Big, Bottom) = Bottom) then Print("min max")
