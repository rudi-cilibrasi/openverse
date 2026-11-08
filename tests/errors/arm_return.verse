# expect: return in an arm of sync or race is not supported yet
F()<suspends>:int =
    X := race:
        block:
            Sleep(1.0)
            return 5
        block:
            Sleep(2.0)
            1
    X
Main()<suspends>:void = Print("{F()}")
