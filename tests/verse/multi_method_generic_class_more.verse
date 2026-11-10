# More methods with several values of generic classes (#283): a recursive
# one, a constrained type parameter, and a field set before the choice
box(t : type) := class:
    A : t
    B : t
    Count(N : int)<computes>:t = if (N > 0) then (A | Count(N - 1)) else B
cbox(t : subtype(comparable)) := class:
    A : t
    B : t
    Eqs()<transacts>:t = (if (A = B) then A else B) | A
mbox(t : type) := class:
    var M : t
    SetBoth(V : t)<transacts>:t =
        set M = V
        M | M
Main()<transacts>:void =
    X := box(int){A := 1, B := 2}
    for (V := X.Count(2)):
        Print("c {V}")
    Y := cbox(int){A := 1, B := 2}
    for (V := Y.Eqs()):
        Print("a {V}")
    Z := mbox(string){M := "m"}
    for (V := Z.SetBoth("n")):
        Print("b {V} {Z.M}")
    if (W := Z.SetBoth("o"), W = "x"):
        Print("never")
    Print("m {Z.M}")
