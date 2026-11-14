# expect: this filter cannot fail
# An if whose branches cannot fail cannot fail, though its condition can
Main():void =
    R := for (X := 1..3, if (X > 1) then 1 else 0) { X }
    Print("{R.Length}")
