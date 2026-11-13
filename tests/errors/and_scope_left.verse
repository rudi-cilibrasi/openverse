# expect: 4:31: unknown identifier 'X'
# A and B and C is (A and B) and C: the inner and is a scope of its own, so C does not see A's names.
Main():void =
    if ((X := 1) and X > 0 and X < 5) { Print("x") }
