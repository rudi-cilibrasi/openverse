# An extension method is a function: its effects, failure and rollback,
# several values and <suspends> are a function's (Book of Verse ch. 6)

cell := class:
    var N:int = 0
(C:cell).Bump(K:int)<transacts>:int =
    set C.N += K
    C.N
(C:cell).BumpUnless(K:int, Limit:int)<transacts><decides>:int =
    set C.N += K
    C.N <= Limit

# several values, taken by for and by if
(I:int).Around():int = I - 1 | I | I + 1
(T:tuple(int, int, int)).Each():int = T(0) | T(1) | T(2)

(I:int).Later()<suspends>:int =
    Sleep(0.01)
    I + 1

Main()<suspends>:void =
    C := cell{}
    Print("{C.Bump(2)} {C.Bump(3)}")
    if (V := C.BumpUnless[1, 10]) then Print("ok {V}")
    if (V := C.BumpUnless[100, 10]) then Print("ok {V}") else Print("undone: {C.N}")
    for (X := 5.Around()) { Print("around {X}") }
    if (X := 5.Around(), X > 5) then Print("first above 5: {X}")
    for (X := (7, 8, 9).Each(), X <> 8) { Print("each {X}") }
    Y := 1.Later()
    T := spawn{10.Later()}
    Print("{Y} {T.Await()}")
