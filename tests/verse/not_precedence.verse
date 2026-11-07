# `not` binds more loosely than the comparisons and more tightly than `and`
# and `or` (spec grammar: Not := Eq | "not" Not; And := Not {and And}).
Main():void =
    X := 1
    Y := 2
    if (not X = Y) then Print("not (1 = 2)")
    if (not X < Y) then Print("wrong") else Print("1 < 2, so not fails")
    if (not X = Y and X < Y) then Print("(not 1 = 2) and 1 < 2")
    if (not X > Y or not X = 1) then Print("(not 1 > 2) or (not 1 = 1)")
    if (not not X = 1) then Print("not not (1 = 1)")
    if (not X + 1 = Y) then Print("wrong") else Print("1 + 1 = 2, so not fails")
