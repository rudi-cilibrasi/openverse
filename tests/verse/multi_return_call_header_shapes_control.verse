# The control of multi_return_call_header_shapes: the same loops with each
# call in both branches of a conditional that picks the first. The output
# is the same.
Cell := class{var N:int = 0}
Ok(S:Cell)<transacts><decides>:void =
    S.N >= 0
# A generic function: adds 1, then its two values.
Gen(S:Cell, A:t, B:t where t:type)<transacts>:t =
    set S.N += 1
    A | B
# One that picks a branch itself.
Cond(S:Cell)<transacts>:int =
    if (S.N > 5) then (1 | 2) else (7 | 8)
# One whose alternatives are calls of the others.
Twice(S:Cell)<transacts>:int =
    Cond(S) | Gen(S, 20, 30)
base := class:
    Vals(S:Cell)<transacts>:int = 4 | 1
derived := class(base):
    Vals<override>(S:Cell)<transacts>:int =
        set S.N += 1
        3 | 1
# An unrelated class with a method of the same name.
other := class:
    Vals(S:Cell)<transacts>:int = 9 | 8
# In a generic function, after a clause that binds a name. Both rows go on
# when P is 5, and the loop's end gives B; the first row returns when P is 6.
Generic(S:Cell, A:t, B:t where t:type)<transacts>:t =
    for (P := S.N + 5, V := if (Ok[S]) then Gen(S, A, B) else Gen(S, A, B)):
        Y := V | A
        if (P > 5):
            return Y
        Print("generic {P} {S.N}")
    B
# After a generator, with a filter after the call: the rows 7 and 8 of
# `Cond` are undone, and `Gen`'s write is kept with its rows 20 and 30.
After(S:Cell)<transacts>:int =
    for (X : array{1, 2}, V := if (Ok[S]) then Twice(S) else Twice(S), V + X >= 21):
        Y := V | V + 100
        if (X = 2, V = 20):
            return Y
        Print("after {X} {V} {Y} {S.N}")
    S.N
# Inside an expression.
Expr(S:Cell)<transacts>:int =
    for (Q := if (Ok[S]) then Gen(S, 1, 2) else Gen(S, 1, 2), V := Q + 10):
        Y := V | V + 100
        if (V = 12):
            return Y
        Print("expr {V} {Y} {S.N}")
    S.N
# In a filter: the row 7 fails it.
Filter(S:Cell)<transacts>:int =
    for (Q := if (Ok[S]) then Cond(S) else Cond(S), Q > 7, V := S.N + 3):
        Y := V | V + 100
        if (V = 3):
            return Y
        Print("filter {V}")
    S.N
# An overridden method, whose name another class has too: the receiver's
# class picks the implementation whose values are the rows.
Method(B:base, S:Cell)<transacts>:int =
    for (V := if (Ok[S]) then B.Vals(S) else B.Vals(S)):
        Y := V | V + 100
        if (V = 1):
            return Y
        Print("method {V} {Y} {S.N}")
    S.N
# The loop's own function.
Own(S:Cell, K:int)<transacts>:int =
    if (K <= 0):
        return 4 | 1
    for (V := if (Ok[S]) then Own(S, K - 1) else Own(S, K - 1)):
        Y := V | V + 100
        if (V = 1):
            return Y
        Print("own {K} {V} {Y}")
    0
Main()<transacts>:void =
    A := Cell{}
    for (X := Generic(A, "x", "y")):
        Print("g {X} {A.N}")
    for (X := Generic(A, 1, 2)):
        Print("g {X} {A.N}")
    B := Cell{}
    for (X := After(B)):
        Print("a {X} {B.N}")
    Print("state {B.N}")
    # The loop's function in a loop of its caller's.
    for (I := 0..1, X := Expr(Cell{})):
        Print("e {I} {X}")
    C := Cell{}
    for (X := Filter(C)):
        Print("f {X} {C.N}")
    D := Cell{}
    for (X := Method(derived{}, D)):
        Print("m {X} {D.N}")
    for (X := Method(base{}, D)):
        Print("m {X} {D.N}")
    for (X := other{}.Vals(D)):
        Print("o {X}")
    for (X := Own(D, 1)):
        Print("s {X}")
