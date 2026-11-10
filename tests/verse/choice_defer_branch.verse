# A block with a defer: of its own as an if's branch (#283), in a for and where the first success is
# taken: the defer: runs as each value leaves the branch; a value typed by where it is (false against
# ?int); a block with a defer: in a recursive function, computed at the call or taken lazily
F(N:int)<transacts>:int = N | N + 1
Rec(N:int)<computes>:int = if (N > 0) then block{ defer: Z := 1; Y := N | 100; Y } else Rec(N - 1)
Gen(A:int, B:int)<computes><decides>:int =
    A <= B
    block{ defer: Z := A; Y := A | A * 10; Y } | Gen[A + 1, B]
Main()<transacts>:void =
    for (I := 1..2, V := (if (I = 1) then { defer: Print("t{I}"); F(10) } else { defer: Print("e{I}"); W := F(20); W * 2 })):
        Print("v {V}")
    for (I := 1..2, V := (if (I = 1) then { defer: Print("t{I}"); 1 | 2 } else { defer: Print("e{I}"); 3 })):
        Print("w {V}")
    if (V := (if (1 > 2) then 0 else { defer: Print("f"); F(5) }), V > 5) { Print("first {V}") }
    for (V:?int := block{ defer: Print("d"); Y := 1 | 2; false }) { Print("q") }
    for (I := 1..2, V:?int := (if (I = 1) then { defer: Print("t"); Z := 1 | 2; option{Z} } else { defer: Print("e"); false })):
        if (W := V?) then Print("o {W}") else Print("none")
    for (X := Rec(2)) { Print("r {X}") }
    for (X := Gen[1, 2]) { Print("gen {X}") }
