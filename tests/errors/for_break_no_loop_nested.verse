# expect: break is only allowed inside loop (not for
# A break in a for's body leaves the loop around the for (#724,
# tests/verse/for_break_loop); nested fors in no loop have none.
Main():void =
    for (X := 1..3):
        for (Y := 1..3):
            if (X = Y) then break
