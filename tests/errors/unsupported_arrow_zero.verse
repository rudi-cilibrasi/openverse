# expect: a lambda (…) => … is a nested function, which openverse does not have (#492
# A lambda of no parameters parses and is refused, as a nested function (#492).
Main():void =
    F := () => 7
    Print(F())
