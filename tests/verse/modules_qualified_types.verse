# the qualified type (M:)c and construction (M:)c{…} (#147)
M := module:
    c<public> := class:
        V:int = 4
Main():void =
    A := (M:)c{V := 5}
    Print("{A.V}")
    B:(M:)c = A
    Print("{B.V}")
