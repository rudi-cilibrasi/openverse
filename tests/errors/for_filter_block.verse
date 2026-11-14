# expect: this filter of a for cannot fail
# A block whose statements cannot fail, nor its value, is a filter that
# cannot fail
Main():void =
    R := for (X := 1..3, block{Print("x"); X}) { X }
    Print("{R.Length}")
