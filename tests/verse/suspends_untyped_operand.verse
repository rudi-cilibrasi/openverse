# an argument with no type of its own before a suspending argument: its
# temporary takes the callee's parameter type, or the type of the array,
# tuple or object's part (#188)
Run(N:int)<suspends>:int =
    Sleep(0.2)
    N
Take2(A:[]int, N:int)<suspends>:int = N + A.Length
Opt(O:?int, N:int)<suspends>:int = if (V := O?) then V + N else N
pr := class:
    A:[]int
    N:int
Main()<suspends>:void =
    C:logic = true
    Print("{Take2(if (C?) then array{} else array{}, Run(5))}")
    Print("{Opt(if (C?) then false else option{1}, Run(5))}")
    X:[][]int = array{if (C?) then array{} else array{}, array{Run(3)}}
    Y:tuple([]int, int) = (if (C?) then array{} else array{}, Run(4))
    Z := pr{A := if (C?) then array{} else array{}, N := Run(5)}
    Print("{X.Length} {Y(1)} {Z.N}")
