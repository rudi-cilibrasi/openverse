# expect: break is only allowed inside loop
Main()<suspends>:void =
    loop:
        sync:
            block:
                Sleep(1.0)
                break
            Sleep(1.0)
