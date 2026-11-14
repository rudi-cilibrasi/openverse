# expect: 8:4: 'R' is already defined; Verse does not allow shadowing
# A local of a generic function with several values, defined twice: named
# as written, not as the inlining renames it.
Rep(X:t, N:int where t:type)<transacts><decides>:[]t =
    N >= 0
    E:[]t = array{}
    R := Rep[X, N - 1] | E
    R := Rep[X, N - 1] | E
    R + array{X}
Main()<transacts>:void =
    for (V := Rep["a", 2]) { Print("{V.Length}") }
