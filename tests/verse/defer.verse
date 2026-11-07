# defer (Book of Verse ch. 7): runs when its scope exits, normally or by
# return or break, last registered first; not when the scope fails

Basic():void =
    Print("start")
    defer:
        Print("deferred 1")
    defer:
        Print("deferred 2")
    Print("end")

Early(N:int):int =
    defer:
        Print("leaving Early({N})")
    if (N > 2):
        return N * 10
    N

Value():int =
    X := 5
    defer:
        Print("after computing {X}")
    X + 1

Loop():void =
    var I:int = 0
    loop:
        defer:
            Print("iteration {I} done")
        set I += 1
        if (I >= 3):
            break

Nested():void =
    defer:
        Print("outer")
    block:
        defer:
            Print("inner")
        Print("in block")
    Print("after block")

Fails()<decides>:void =
    defer:
        Print("never printed")
    1 = 2

Main():void =
    Basic()
    Print("{Early(1)} {Early(5)}")
    Print("{Value()}")
    Loop()
    Nested()
    if (Fails[]) then Print("ok") else Print("failed, no defer")
