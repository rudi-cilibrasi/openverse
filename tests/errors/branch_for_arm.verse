# expect: branch cannot be in a loop or for body
Main()<suspends>:void =
    for (I := 1..2):
        sync:
            branch:
                Sleep(1.0)
            Sleep(1.0)
