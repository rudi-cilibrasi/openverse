# Overloaded functions with several values (#283) whose overloads call the function's own name: the
# other overload (inlined there, as any call of a function with several values), or the same one
# (recursive, taken lazily, as a generator), each call taking the overload its arguments fit
F(N : int):int = N | F("x")
F(S : string):int = 1 | 2
# (a generator, its string overload calling it)
Down(N:int):int = if (N <= 0) then 0 else (N | Down(N - 1))
Down(S:string):int = Down(S.Length) * 10
# (by arity: the two-parameter overload calls the one-parameter one, which prints)
G(A:int)<transacts>:int =
    Print("g {A}")
    A | -A
G(A:int, B:int)<transacts>:int = G(A) + G(B)
Main()<transacts>:void =
    for (X := F(1)) { Print("a {X}") }
    for (X := Down(3)) { Print("b {X}") }
    for (X := Down("ab")) { Print("c {X}") }
    if (X := Down(5), X < 4) then Print("d {X}")
    for (X := G(1, 2), X > 0) { Print("e {X}") }
