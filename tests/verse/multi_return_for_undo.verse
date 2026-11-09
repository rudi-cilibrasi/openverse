# A return in a branch, in a for with a filter after the call (#283, tim-e1's
# case on #312): the branch's print is undone with the rejected value, as
# without the return (the choice between the branches comes before it)
F(X : int)<transacts>:int =
    Y := X | X + 1
    if (Y = 99):
        return 0
    else:
        Print("e{Y}")
    Y
Main()<transacts>:void =
    for (Z := F(1), Z > 1):
        Print("z {Z}")
