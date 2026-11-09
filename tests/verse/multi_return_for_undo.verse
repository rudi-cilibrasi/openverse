# A return in a function with several values, in a for with a filter after
# the call (#283, tim-e1's cases on #312): the prints in the branch and
# before the if are undone with the rejected value, as without the return
F(X : int)<transacts>:int =
    Y := X | X + 1
    if (Y = 99):
        return 0
    else:
        Print("e{Y}")
    Y
Pre(X : int)<transacts>:int =
    Y := X | X + 1
    Print("pre{Y}")
    if (Y = 99):
        return 0
    Y
Main()<transacts>:void =
    for (Z := F(1), Z > 1):
        Print("z {Z}")
    for (Z := Pre(1), Z > 1):
        Print("z {Z}")
