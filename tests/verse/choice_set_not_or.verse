# A set with a choice or a call with several values in its path or value, inside not (…) and on the left
# of or (#283): the first success is taken, not's effects rolled back, or's kept
Two(N:int)<transacts>:int = N | N + 1
Show(A:[]int)<transacts>:void =
    if (P := A[0], Q := A[1], R := A[2]) then Print("{P} {Q} {R}")
Main()<transacts>:void =
    var A:[]int = array{0, 0, 0}
    if (not (set A[1 | 2] = 5)) then Print("no") else Print("yes")
    Show(A)
    if ((set A[0 | 1] = 7) or A.Length > 5) then Print("or")
    Show(A)
    if ((set A[5 | 1] = 8) or A.Length > 5) then Print("or2")
    Show(A)
    if (not (set A[Two(3)] = 9)) then Print("none") else Print("some")
    Show(A)
    if ((set A[Two(1)] = 4) or A.Length > 5) then Print("or3")
    Show(A)
    if (not (set A[0] = (1 | 2))) then Print("n4") else Print("y4")
    var X:int = 0
    if ((set X = 10 | 20) or A.Length > 5) then Print("x {X}")
