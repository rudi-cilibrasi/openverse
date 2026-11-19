# Rationals of ints beyond 64 bits (#724): X / Y reduces exactly and its
# parts are ints of any length, so Floor and Ceil give ints beyond 64 bits;
# the rational arithmetic extension (#489) also reduces before it checks
# the parts' length, which is the ints' (2^20 bits).
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

Main():void =
    Top:int = 9223372036854775807
    Big := Top + 1
    if (R := (Big * Big + 1) / Big) then Print("floor {Show(Floor(R))} ceil {Show(Ceil(R))}")
    if (R := (Big * 6) / (Big * 4), R = 3 / 2) then Print("reduced {Floor(R)} {Ceil(R)}")
    if (R := 1 / Top, S := R / 2, Floor(S * Big * Top * 2) = Big) then Print("denominator beyond 64 bits")
    if (R := 1 / Top, S := R * R, Floor(1 / S) = Top * Top) then Print("product of denominators")
    if (R := -Big / 3, R < -Top / 3, Floor(R) = -3074457345618258603) then Print("ordering")
    if (R := Top / 2, S := R + R + 1 / 2, Floor(S) = Top) then Print("sum")
