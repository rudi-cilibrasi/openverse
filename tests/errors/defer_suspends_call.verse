# expect: Child suspends, and a defer cannot suspend
# A defer may spawn a suspending call (#724), not call one.
Child()<suspends>:void = Sleep(0.1)
Run()<suspends>:void =
    defer:
        Child()
    Sleep(0.0)
Main()<suspends>:void = Run()
