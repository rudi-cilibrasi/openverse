# expect: 8:22: a choice (a | b) cannot be lifted from a construction of dd that does not give field 'Y'
# (a refused operand of a comparison chain is kept: no endless lifting)
G()<transacts>:int =
    Print("g")
    7
dd := struct { X : int; Y : int = G(); Z : int }
Main()<transacts>:void =
    if (0 < dd{Z := 1 | 2, X := 0}.Z):
        Print("lt")
