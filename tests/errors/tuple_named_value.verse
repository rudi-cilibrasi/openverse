# expect: a tuple with a named element (?Name := …) is not supported: the pinned Book of Verse does not settle such values
# (its DefaultNamed tests refuse every use of one)
Main():void =
    X := (0, ?A := 1, ?B := 2)
    Print("made")
