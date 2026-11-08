# expect: branch cannot be in a loop or for body
Main()<suspends>:void =
    loop:
        branch:
            Sleep(1.0)
        break
