# A break in first-success clauses with a choice, in a <suspends> function's
# loop (#283): the clauses cannot wait, the loop around them can.
cell := class { var N:int = 0 }
Two(N:int):int = N | N + 1
Upto(H:cell, A:int, B:int)<transacts><decides>:int =
    A <= B
    set H.N += 1
    A | Upto[H, A + 1, B]
Run(H:cell, S1:int, S2:int, S3:int)<suspends>:int =
    var V:int = 0
    defer: Print("function cleanup V={V} H={H.N}")
    var I:int = 0
    loop:
        defer: Print("loop cleanup I={I} V={V} H={H.N}")
        set I += 1
        Sleep(0.0)
        if (A := (Two(0) | Two(2)), set V += A, B := (Two(0) | Two(2)), A * B = S1 + I, break) then Print("not reached")
        if (X := Upto[H, 1, 4], X = S2 - I, set V += 100, break) then Print("not reached")
        R := for (C := 1..2, D := (if (Y := 1 | 2, set V += 1000, Y * C = S3 + I, break) then 1 else 0)):
            C + D
        Sleep(0.0)
        Print("iteration {I} rows {R.Length} V={V} H={H.N}")
        if (I = 3) then break
    V
Main()<suspends>:void =
    H := cell{}
    Print("result {Run(H, 20, 20, 20)} {H.N}")
    Print("result {Run(H, 20, 6, 20)} {H.N}")
    Print("result {Run(H, 20, 20, 2)} {H.N}")
    Print("result {Run(H, 5, 20, 20)} {H.N}")
