# Overloaded functions with several values (#283): a nested call, a call in an
# inlined body and in a method, an overload with one value called as written
Two(N : int):int = N | N * 10
Two(S : string):string = S | S + "!"
Pick(S : string):int = S.Length
Pick(N : int):int = N | N + 1
H(N : int):int = Two(N) + 1
c := class:
    K : int = 3
    Run()<transacts>:void =
        for (V := Two(K)):
            Print("m {V}")
Main()<transacts>:void =
    for (X := Two(Two(1))):
        Print("a {X}")
    for (X := H(2)):
        Print("b {X}")
    c{}.Run()
    Print("d {Pick("abc")}")
    for (X := Pick(5), S := Two("z")):
        Print("e {X} {S}")
