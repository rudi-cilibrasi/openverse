# a field named like a soft built-in leaves the built-in to its class's methods (#132 review)
thing := class:
    Round:int = 7
    Sqrt:float = 9.0
    Go():void =
        if (R := Round[2.5]) then Print("round {R} {Sqrt(4.0)} {Self.Round} {Self.Sqrt}")
Main():void = thing{}.Go()
