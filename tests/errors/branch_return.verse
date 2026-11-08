# expect: return is not allowed in a branch
F()<suspends>:int =
    branch:
        Sleep(1.0)
        return 1
    0
Main()<suspends>:void = Print("{F()}")
