# expect: expected int, found void
Bad(N:int):int =
    loop:
        loop:
            break
        if (N = 0) then break
        return 7
Main():void = {}
