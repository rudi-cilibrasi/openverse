# a generic function with several values, inlined at its calls at two types: its parameters and value at the arguments' and values' own types (#235)
Pick(X:t, Y:t where t:type):t = X | Y
Main():void =
    for (Z := Pick(1, 2)) { Print("{Z}") }
    for (S := Pick("a", "b")) { Print(S) }
    if (Z := Pick(3, 4), Z > 3) then Print("first {Z}")
