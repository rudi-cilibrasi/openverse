# a branch in a generic function that calls itself at ever bigger types (#244)
Tick(X:t, N:int where t:type)<suspends>:void =
    branch:
        Sleep(0.2)
        Print("tick {N}")
    if (N > 0) then Tick(array{X}, N - 1)
    Sleep(0.5)
Main()<suspends>:void = Tick(1, 2)
