# expect: this filter of a for is a literal, which cannot fail
Main():void =
    R:[]int = for(X := 1..4; 1) { X }
    Print("{R.Length}")
