# ToDiagnostic of an int beyond 64 bits gives its decimal digits (#724), as
# the Book of Verse's verse_vm_only cases expect
# (Intrinsics/ToDiagnostic.versetest:35-40), though ToString refuses it.
Show(V:any):void = Print(ToDiagnostic(V).String)

Main():void =
    Show((9223372036854775807 + 0) * 1 + 0)
    Show((9223372036854775807 + 1) * 1 + 0)
    Show((9223372036854775807 + 1) * 2 - 1)
    Show((9223372036854775807 + 1) * 2 + 0)
    Show((9223372036854775807 + 1) * 2 + 1)
    Show(10000000000 * 10000000000)
    Show(-(10000000000 * 10000000000) * 10000000000 - 7)
    Show(-9223372036854775807 - 1)
    Show(-9223372036854775807 - 2)
    if (R := (10000000000 * 10000000000 + 1) / 10000000000) then Show(R)
    Show(array{(9223372036854775807 + 1) * 1000000000000000000})
