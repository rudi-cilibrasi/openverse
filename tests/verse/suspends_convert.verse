# a suspending call converted to another option type, and effects on
# suspends functions (#156, review of #158)
GetO(N:int)<suspends>:?int =
    Sleep(0.01)
    option{N}
UseR(X:?rational):int = if (Y := X?) then Floor(Y) else 0
F(N:int)<suspends><computes>:int =
    Sleep(0.01)
    N + 1
G(N:int)<suspends><reads>:int =
    F(N) + 1
Main()<suspends>:void =
    X:?any = GetO(1)
    Print("{UseR(GetO(5))} {G(1)}")
