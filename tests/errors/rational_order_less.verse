# expect: '<' does not order a rational: it compares two ints or two floats, and a rational has only = and <> (found rational and rational
# (#724) Epic's compiler has no `<` of rationals (UEFN 43.12, error 3509,
# "No overload of the function `operator'<'` matches the provided arguments
# (:rational,:rational)": differential/rat-ordering), and the Book declares
# the relational operators for int and float only (ch. 4).
Main():void =
    if (A := 1 / 3, B := 1 / 2, A < B):
        Print("less")
