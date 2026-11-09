# looking up a key in a map whose values never come (#297 follow-up): the
# lookup, a few statements ending in an index, is taken to the expected
# type like any other read of such a value
F(K:int):int =
    M := if (K = 2) then map{1 => return 5} else map{}
    if (Z:int = M[1]) then Z else 0
G(K:int):int =
    M := if (K = 2) then map{"a" => return 6} else map{}
    if (Z:string = M["a"]) then Z.Length else 1
Main():void =
    Print("{F(2)} {F(3)} {G(2)} {G(3)}")
