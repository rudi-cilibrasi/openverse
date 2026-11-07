# expect: 3:33: no ToString for rational (Verse defines it for int, char, char32 and string)
Main():void =
    if (R := 1 / 2) then Print("{R}")
