# expect: break is only allowed inside loop (not for
# The loop a break leaves is one of its own function: a for in a function
# called from a loop has none (#724).
Each(Xs:[]int):void =
    for (X : Xs):
        if (X > 1) then break
Main():void =
    loop:
        Each(array{1, 2, 3})
        break
