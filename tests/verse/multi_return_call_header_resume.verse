# (#761, #686) A loop left by a return, in a function with several values,
# whose header calls a function with several values where a clause is
# written: `V := Many(S)`. The call is inlined into the header that the
# loop's cursor steps, so its values are rows like a written choice's: a row
# that reaches no body is undone back to the value it is in, and a body
# choice resumes the header from its row.
# `Many` adds 1 before its values 3, 4, 6. `Inner` adds 100 and has an
# element for an even V only, so the row V = 3 is undone. V = 4 goes on to
# the next row, V = 6 returns. Each alternative of `Y` at V = 4 runs the row
# V = 6 again.
# The same loop with `Many`'s code written in the header is
# multi_return_call_header_resume_control.
Cell := class{var N:int = 0}
Many(S:Cell)<transacts>:int =
    set S.N += 1
    3 | 4 | 6
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (Mod[V, 2] = 0) then array{V * 10} else array{}
Find(S:Cell)<transacts>:int =
    var T:int = 0
    for (V := Many(S), W : Inner(S, V)):
        set S.N += 1000
        Y := W | W + 1
        if (V = 6):
            return Y * 100 + T
        set T += Y
        Print("advance {V} {W} {Y} {T} {S.N}")
    S.N
# No row reaches the body: the call's write is undone with the rows.
Odd(S:Cell)<transacts>:int =
    for (V := Many(S), W : Inner(S, V + V + 1)):
        Y := W | W + 1
        if (V = 6):
            return Y
        Print("odd {V}")
    S.N
Main()<transacts>:void =
    # Every value: the writes of the values taken are kept.
    A := Cell{}
    for (X := Find(A)):
        Print("all {X} {A.N}")
    Print("state {A.N}")
    # The fourth value: the three before it are rejected and undone, so
    # `T` is 41, not 81, and the write of the first `advance` is gone.
    B := Cell{}
    if (X := Find(B), X = 6141) then Print("fourth {X} {B.N}") else Print("missed")
    Print("state {B.N}")
    # No value is taken: everything is undone.
    C := Cell{}
    if (X := Find(C), X = 0) then Print("bad") else Print("none {C.N}")
    D := Cell{}
    for (X := Odd(D)):
        Print("odd {X} {D.N}")
