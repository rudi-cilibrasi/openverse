# Args is openverse's (the command line's), not the Book's: a program that
# binds the name itself, a local's here, has its own (the Book's tests,
# DefaultNamed.versetest:274, Math/Math.versetest:84).
Sum(A:int, B:int, ?C:int = 3):int = A + B + C
Main():void =
    Args:tuple(int, int) = (1, 2)
    Print("{Sum(Args)} {Args(1)}")
