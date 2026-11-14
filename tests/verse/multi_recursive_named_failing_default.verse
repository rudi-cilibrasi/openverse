# Recursive functions with several values whose omitted default fails (#283):
# the call fails, which ends the recursion. openverse's reading of a default
# (--extended-defaults); the Book refuses a default that can fail
# (DefaultNamed.versetest:820), which multi_recursive_named follows.
Arr:[]int = array{10,20}
Maybe(N:int,?V:int=Arr[N])<computes><decides>:int = V | Maybe[N+1]
Pick(N:int,?V:int=Arr[N])<computes><decides>:int = N | V
Eager(N:int,?K:int=2)<computes><decides>:int =
    if (N>0) then (Pick[N,?V:=K] | Pick[N] | Eager[N-1]) else 0
Main()<transacts>:void =
    for (X := Maybe[0]): Print("maybe {X}")
    if (X := Maybe[0], X > 10) then Print("maybe first {X}")
    for (X := Eager[2]): Print("eager {X}")
