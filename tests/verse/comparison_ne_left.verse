# `<>` is left-associative: its left operand is the comparisons before it,
# whose value is the leftmost operand; the other comparisons chain (Book of
# Verse tests, Operators/Associativity.versetest 6-33).
Main():void =
    if (not 1 <> 2 <> 1) then Print("left-assoc <>")
    if (1 <> 2 <> 3) then Print("1 <> 3")
    if (0 <= 5 <= 9) then Print("chain")
    if (not 1 < 3 < 2) then Print("chain <")
    if (X := (1 <> 2 <> 3)) then Print("value {X}")
    if (1 < 2 <> 1) then Print("mixed") else Print("not mixed")
