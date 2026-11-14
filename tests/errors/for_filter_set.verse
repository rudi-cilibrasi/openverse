# expect: this filter cannot fail
# A set among a for's clauses is a filter that cannot fail
Main():void =
    var T:int = 0
    R := for (X := 1..3, set T += X) { X }
    Print("{R.Length} {T}")
