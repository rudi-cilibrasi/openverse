# expect: this filter of a for cannot fail
# A print among a for's clauses is a filter that cannot fail (Book of Verse
# ch. 7, "Each filter must be failable")
Main():void =
    R := for (X := 1..3, Print("x {X}"), X > 1) { X }
    Print("{R.Length}")
