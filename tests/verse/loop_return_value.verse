Find(N:int):int =
    var I:int = 0
    defer: Print("find cleanup")
    loop:
        if (I = N) then return I * 2
        set I += 1

Nested():string =
    loop:
        loop:
            break
        return "nested"

ForReturn():int =
    loop:
        for (I : array{2, 5, 8}):
            if (I > 3) then return I

Main():void =
    Print("{Find(3)}")
    Print(Nested())
    Print("{ForReturn()}")
