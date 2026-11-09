# a generic function with several values whose type parameter is comparable, its last expression a branchy if (#235)
Uniq(X:t, Y:t where t:subtype(comparable)):t = if (X <> Y) then (X | Y) else X
Main():void =
    for (Z := Uniq(1, 2)) { Print("{Z}") }
    for (Z := Uniq("s", "s")) { Print(Z) }
