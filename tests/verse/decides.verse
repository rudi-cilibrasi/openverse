# <decides> functions, Euclidean Mod/Quotient, case.
Half(N:int)<decides>:int =
    Mod[N, 2] = 0
    Quotient[N, 2]

ValidateAge(Age:int)<decides>:int =
    Age >= 0
    Age <= 150
    Age

Describe(N:int):string =
    case (N):
        0 => "zero"
        1 => "one"
        _ => "many"

Main():void =
    for (I := -3..4):
        if (H := Half[I]) then Print("{I} -> {H}") else Print("{I} is odd")
    Print("Mod[-7, 2] = {Mod[-7, 2] or -1}, Quotient[-7, 2] = {Quotient[-7, 2] or -1}")
    Print("Mod[7, -2] = {Mod[7, -2] or -1}, Quotient[7, -2] = {Quotient[7, -2] or -1}")
    if (not Mod[1, 0]) { Print("Mod by zero fails") }
    Print("Floor(-5 / 2) = {Floor(-5 / 2) or 0}, Ceil(-5 / 2) = {Ceil(-5 / 2) or 0}")
    if (A := ValidateAge[42]) { Print("valid age {A}") }
    if (not ValidateAge[200]) { Print("200 is not a valid age") }
    Print("{Describe(0)} {Describe(1)} {Describe(7)}")
