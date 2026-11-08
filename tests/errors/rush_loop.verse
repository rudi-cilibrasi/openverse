# expect: rush cannot be in a loop or for body
W()<suspends>:int =
    Sleep(1.0)
    1
Main()<suspends>:void =
    loop:
        X := rush:
            W()
            W()
        break
