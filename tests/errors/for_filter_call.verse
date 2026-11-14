# expect: this filter of a for cannot fail
# A call of a function that cannot fail, its value unused, is a filter that
# cannot fail
Double(X:int):int = X * 2
Main():void =
    R := for (X := 1..3, Double(X)) { X }
    Print("{R.Length}")
