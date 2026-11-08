# Concatenate of nested empty arrays, and ReplaceAll in a <computes> function (#150 review)
F(S:string)<computes>:string = S.ReplaceAll("a", "b")
Main():void =
    W:[]int = Concatenate(array{array{}, array{1}})
    Z:[]int = Concatenate(array{})
    Print("{W.Length} {Z.Length} {F("banana")}")
