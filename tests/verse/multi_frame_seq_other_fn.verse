# (#283) A recursive function's code may call another function with several
# values as a choice point: the callee's code is taken by the same machine as
# the function's own calls, as a call of the function is, a frame after it
# running on each of its values. A non-recursive callee (its clauses a
# failure context of their own: when they fail it has no values and, in a
# for, what came before the call stays), a recursive one, a generic one, a
# method, one with a named parameter or a return, one whose values are of
# another type, a generic one at another type than the function's, one with a condition that takes a third one's values, and a
# callee of a mutual pair.
Two(N:int)<transacts>:int = N | N + 5
Digits(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        Print("digits {N}")
        Digits(N - 1) * 10 + Two(N)
Big(N:int)<transacts><decides>:int =
    Print("big {N}")
    N > 1
    N | N * 10
Boundary(N:int)<transacts><decides>:int =
    N > 0
    X := Boundary[N - 1] | N
    Print("x {N} {X}")
    X + Big[X]
Down(N:int)<transacts><decides>:int =
    N > 0
    Print("down {N}")
    N | Down[N - 1]
Sum(N:int)<transacts><decides>:int =
    N >= 0
    if (N = 0) then 0 else Sum[N - 1] * 10 + Down[N]
Either(X:t, Y:t where t:type)<transacts>:t = X | Y
Gen(N:int)<transacts>:int =
    if (N <= 0) then 0 else Either(Gen(N - 1), N * 10)
dice := class:
    Sides:int
    Roll()<transacts>:int = 1 | Sides
Rolls(N:int, D:dice)<transacts>:int =
    if (N <= 0) then 0 else Rolls(N - 1, D) * 10 + D.Roll()
Pick(A:int, ?B:int = 7)<transacts>:int = A | B
Picks(N:int)<transacts>:int =
    if (N <= 0) then 0 else Picks(N - 1) + Pick(N, ?B := 100) + Pick(N * 10)
Early(N:int)<transacts>:int =
    if (N > 1):
        return N | 10
    N + 100
Returns(N:int)<transacts>:int = if (N <= 0) then 0 else Returns(N - 1) + Early(N)
Word(N:int)<transacts>:string =
    Print("word {N}")
    "a" | "bb"
Lengths(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        S := Word(N)
        Print("s {N} {S}")
        Lengths(N - 1) + S.Length
Up(N:int)<transacts>:int = N | N + 1
Gate(N:int)<transacts>:int =
    if (Up(N) > 1) then (N | 100) else -N
Gates(N:int)<transacts>:int = if (N <= 0) then 0 else Gates(N - 1) + Gate(N)
Sign(N:int)<transacts>:int = N | -N
Even(N:int)<transacts>:int = if (N <= 0) then 0 else Odd(N - 1) + Sign(N)
Odd(N:int)<transacts>:int = if (N <= 0) then 1 else Even(N - 1) * 10
Both(X:t, Y:t where t:type)<transacts>:t = X | Y
Strs(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        S := Both("x", "yy")
        Strs(N - 1) * 10 + S.Length
Main()<transacts>:void =
    for (V := Digits(2)) { Print("v {V}") }
    if (V := Digits(2), V > 20) then Print("taken {V}")
    for (V := Boundary[2]) { Print("v {V}") }
    for (V := Sum[2]) { Print("v {V}") }
    if (V := Sum[2], V < 12) then Print("taken {V}")
    for (V := Gen(2)) { Print("v {V}") }
    for (V := Rolls(2, dice{Sides := 6})) { Print("v {V}") }
    for (V := Picks(1)) { Print("v {V}") }
    for (V := Returns(2)) { Print("v {V}") }
    for (V := Lengths(2)) { Print("v {V}") }
    if (V := Lengths(2), V > 3) then Print("taken {V}")
    for (V := Gates(2)) { Print("v {V}") }
    for (V := Even(3)) { Print("v {V}") }
    for (V := Strs(2)) { Print("v {V}") }
