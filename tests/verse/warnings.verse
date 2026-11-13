# Warnings (the Book of Verse's 2000, 2002 and 2302): the compiler reports
# them on standard error and compiles the program all the same
light := enum{Red, Amber, Green}
# a `_` after arms that name every value of a closed enum is never reached
Next(L:light):light =
    case (L):
        light.Red => light.Green
        light.Amber => light.Red
        light.Green => light.Amber
        _ => light.Red
# a value returned from a function whose result is void is discarded
Log(X:int):void =
    Print("log {X}")
    return X + 1
# code after a return, or after an if both of whose branches leave
Pick(X:int):int =
    if (X > 2):
        return 1
    else:
        return 2
    Print("never")
    3
# code after a loop that only a return leaves
Count(Limit:int):int =
    var I:int = 0
    loop:
        set I += 1
        if (I >= Limit) then return I
    0
# a jump out of an operand: the tuple is never made, the not takes the failure
Odd(K:int):int =
    if (not (K = 2, return 42)) then 7 else 8
# none: code after a for whose body returns, or after a race only one of whose arms does
First(Xs:[]int):int =
    for (X : Xs):
        return X
    0
Main():void =
    Print("{ToString(Pick(3))} {Count(4)} {Odd(2)} {Odd(3)} {First(array{5, 6})}")
    Log(1)
    if (Next(light.Red) = light.Green) then Print("green")
