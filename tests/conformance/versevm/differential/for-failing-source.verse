# A for whose source or range bound fails: zero iterations, the for itself
# does not fail, and what the failing source wrote is undone.
# Tests LANGUAGE.md, Readings, "A failing for source": "zero iterations, for
# an iterated source (X : F[]) and a range bound (I := 1..F[]) alike, what
# the source did rolled back ...; the for itself does not fail" (the Book's
# FlowControl/for.versetest:317, ch. 7: "that iteration is skipped").
# OpenVerse prints (Lean and C agree):
#   0 0 0 2 N 0
Main():void =
    G:[][]int = array{array{1, 2}}
    A:[]int = array{4}
    R := for (X : G[3]) { X }
    S := for (I := 1..A[2]) { I }
    var N:int = 0
    T := for (I := 1..(set N += 1; A[5])) { I }
    U := for (X : G[0]) { X * 2 }
    Print("OVPROBE {R.Length} {S.Length} {T.Length} {U.Length} N {N}")
