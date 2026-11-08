# cancellation unwinds a loser's whole call chain, innermost first; arms share variables; sync and race nest; arms woken in the same tick run in source order (#156)
Inner(Tag:string)<suspends>:int =
    defer:
        Print("inner {Tag} unwound")
    Sleep(10.0)
    Print("inner {Tag} finished")
    1
Outer(Tag:string)<suspends>:int =
    defer:
        Print("outer {Tag} unwound")
    X := Inner(Tag)
    X + 1
Tick(Name:string, N:int)<suspends>:void =
    var I:int = 0
    loop:
        if (I >= N) then break
        Sleep(1.0)
        set I += 1
        Print("{Name} tick {I}")
Main()<suspends>:void =
    # a loser deep in a call chain: each frame's defers run, innermost first
    R := race:
        Outer("a")
        block:
            Sleep(1.0)
            7
    Print("race {R}")
    # arms sharing a variable
    var Count:int = 0
    sync:
        block:
            Sleep(1.0)
            set Count += 1
            Print("left sees {Count}")
        block:
            Sleep(2.0)
            set Count += 10
            Print("right sees {Count}")
    Print("count {Count}")
    # nested: a sync inside a race arm, a race inside a sync arm
    Z := race:
        block:
            P := sync:
                Tick("x", 3)
                Tick("y", 2)
            "sync done"
        block:
            Sleep(2.5)
            "timeout"
    Print(Z)
    Q := sync:
        race:
            block:
                Sleep(1.0)
                1
            block:
                Sleep(3.0)
                3
        block:
            Sleep(2.0)
            2
    Print("{Q(0)} {Q(1)}")
    # same-tick order: arms in source order
    sync:
        block:
            Sleep(1.0)
            Print("first arm")
        block:
            Sleep(1.0)
            Print("second arm")
