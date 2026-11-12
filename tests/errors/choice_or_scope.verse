# expect: 5:38: unknown identifier 'Y'
# A name bound on the right of or, with a choice, does not escape the or (#283).
Main():void =
    O:?int = false
    if (O? or (Y := 3 | 4)) { Print("{Y}") }
