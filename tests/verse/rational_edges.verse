# rationals at the edges of int (#116): normalising never overflows unless the numerator is out of range
Main():void =
    M := -9223372036854775807 - 1
    if (R := M / 2) then Print("{Floor(R)}")
    if (R := M / M) then Print("{Floor(R)}")
    if (R := 0 / M) then Print("{Floor(R)} {Ceil(R)}")
    if (R := M / 3) then Print("{Floor(R)} {Ceil(R)}")
    if (R := 6 / -4) then Print("{Floor(R)} {Ceil(R)}")
    if (R := -6 / -4, R = 3 / 2) then Print("signs")
    if (R := 9223372036854775807 / -1) then Print("{Floor(R)}")
    if (R := M / -3) then Print("{Floor(R)}")
