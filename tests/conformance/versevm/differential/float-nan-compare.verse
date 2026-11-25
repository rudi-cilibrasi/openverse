# Comparisons with NaN: equality, ordering, <>.
# Tests LANGUAGE.md, Readings, "NaN < X": "fails (IEEE: NaN orders with
# nothing); NaN = NaN succeeds (the Book)"; float: "NaN equals NaN, and so
# NaN <= NaN and NaN >= NaN succeed (the API's reading, #132); otherwise NaN
# orders with nothing". IEEE comparisons would give n for eq, le, ge and y
# for ne. Each letter: y the comparison succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   nan-nan eq y ne n lt n le y ge y gt n
#   nan-one lt n gt n eq n ne y le-inf n | inf eq y lt y
Main():void =
    Z:float = 0.0
    N:float = Z / Z
    A := if (N = N) then "y" else "n"
    B := if (N <> N) then "y" else "n"
    C := if (N < N) then "y" else "n"
    D := if (N <= N) then "y" else "n"
    E := if (N >= N) then "y" else "n"
    F := if (N > N) then "y" else "n"
    Print("OVPROBE nan-nan eq {A} ne {B} lt {C} le {D} ge {E} gt {F}")
    G := if (N < 1.0) then "y" else "n"
    H := if (1.0 < N) then "y" else "n"
    I := if (N = 1.0) then "y" else "n"
    J := if (N <> 1.0) then "y" else "n"
    K := if (N <= Inf) then "y" else "n"
    Print("OVPROBE nan-one lt {G} gt {H} eq {I} ne {J} le-inf {K}")
    P := if (Inf = Inf) then "y" else "n"
    Q := if (-Inf < Inf) then "y" else "n"
    Print("OVPROBE inf eq {P} lt {Q}")
