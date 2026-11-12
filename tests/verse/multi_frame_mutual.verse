# (#283) Return frames in a mutually recursive group: one continuation for the
# group, each frame the code after a call of any of its functions.
Ev(N:int)<transacts><decides>:int =
    N >= 0
    Print("ev {N}")
    N | Od[N - 1] * 10
Od(N:int)<transacts><decides>:int =
    N >= 0
    Ev[N - 1] + 1 | N
Main()<transacts>:void =
    for (V := Ev[3]) { Print("v {V}") }
    if (V := Ev[3], V > 15) then Print("first {V}")
    if (V := Od[2], V > 15) then Print("never") else Print("none")
