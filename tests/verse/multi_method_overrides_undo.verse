# The dispatch of an overridden method with several values comes before the
# receiver's effects (#283): in a for, a rejected value undoes them, as a call does
shape := class:
    K : int
    Sizes()<transacts>:int = K | K + 1
big := class(shape):
    Sizes<override>()<transacts>:int = 1000
G(S : string, O : shape)<transacts>:shape =
    Print(S)
    O
Main()<transacts>:void =
    for (X := G("recv", big{K := 1}).Sizes(), X > 5000):
        Print("never {X}")
    for (X := G("r2", shape{K := 1}).Sizes(), X > 1):
        Print("x {X}")
    Print("done")
