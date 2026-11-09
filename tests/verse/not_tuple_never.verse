# `return`, `break` and `Err()` as an element of the tuple `not` tests (#285),
# and as an element of a tuple with an expected type
Find(K:int):int =
    if (not (K = 2, return 42)) then 7 else 8
Dec(K:int)<decides>:int =
    not (K = 2, return 42)
    K
Filt(K:int):int =
    var S:int = 0
    for (I := 0..3, not (I = K, return 40 + I)) { set S += I }
    S
Brk(K:int):int =
    var N:int = 0
    loop:
        set N += 1
        if (not (N = K, break)) then {} else {}
        if (N > 5) then break
    N
G(I:int)<decides>:int = I | I + 1 | I + 2 | I + 3
Gen(K:int):tuple(int, int, logic) =
    if (X := G[0], not (X = K, return (42, 99, true)), X = 3) then (X, 0, false) else (0, 0, false)
# with an expected type, such an element is checked against it, as before
Typed(K:int):int =
    T:tuple(int, int) = (1, if (K = 2) then return 3 else K)
    T(1)
Main():void =
    Print("{Find(2)} {Find(3)}")
    if (V := Dec[2]) then Print("{V}") else Print("fail")
    if (V := Dec[3]) then Print("{V}") else Print("fail")
    Print("{Filt(2)} {Filt(9)}")
    Print("{Brk(3)} {Brk(9)}")
    R := Gen(2)
    Print("{R(0)} {R(1)}")
    Q := Gen(9)
    Print("{Q(0)} {Q(1)}")
    Print("{Typed(2)} {Typed(5)}")
