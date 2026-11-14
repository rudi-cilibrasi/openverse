# expect: nothing leaves this loop, no break of its own and no return
Count():void =
    var I:int = 0
    loop:
        set I += 1
        loop:
            if (I > 3) then break
Main():void = Count()
