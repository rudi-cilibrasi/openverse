# a rush loser that runs return after the rush ended unwinds once and ends there (#181)
F()<suspends>:int =
    Q := rush:
        block:
            Sleep(0.5)
            1
        block:
            defer:
                Print("r1 defer")
            Sleep(1.0)
            return 50
    Sleep(3.0)
    Q
Main()<suspends>:void = Print("{F()}")
