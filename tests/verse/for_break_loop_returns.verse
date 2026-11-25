# A break in a for's body beside returns, in a <decides> function, in a
# for whose value is used, and in a method (#724, for_break_loop).
First(Xs:[]int, Limit:int):int =
    var Acc:int = 0
    loop:
        for (X : Xs):
            if (X < 0) then return -1
            set Acc += X
            if (Acc > Limit) then break
        return Acc
    0 - Acc
Dec(Xs:[]int)<transacts><decides>:int =
    var Acc:int = 0
    loop:
        for (X : Xs):
            set Acc += X
            if (X = 0) then break
        break
    Acc > 0
    Acc
G(Xs:[]int):int =
    loop:
        V := for (X : Xs):
            if (X = 3) then break
            X * 2
        return V.Length
    -7
c := class:
    var N:int = 0
    M(Xs:[]int):void =
        loop:
            for (X : Xs, X > 1):
                set N += X
                break
            break
Main():void =
    Print("{First(array{1,2,3}, 100)} {First(array{1,2,3}, 2)} {First(array{1,-2,3}, 100)}")
    Print("{if (V := Dec[array{1,2,0,5}]) then V else -1} {if (V := Dec[array{0}]) then V else -1}")
    Print("{G(array{1,2})} {G(array{1,3})}")
    O := c{}
    O.M(array{1,5,7})
    Print("{O.N}")
