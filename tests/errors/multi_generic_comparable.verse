# expect: 7:18: Same's type argument for t must be comparable, and thing is a class
# (#235, review of #282) an inlined generic call's comparable type parameter is checked, as at a call
thing := class:
    V:int = 0
Same(X:t, Y:t where t:subtype(comparable)):t = if (X = Y) then X else (X | Y)
Main():void =
    for (Z := Same(thing{}, thing{})) { Print("{Z.V}") }
