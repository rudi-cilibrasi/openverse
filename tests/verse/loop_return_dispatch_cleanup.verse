# (#764) A loop return of several values from a `for` over a call of an
# overridden method, with a `defer:` in the loop's body, taken by a `for`
# and by an `if`, which takes the first value its conditions hold for. Each
# returned value runs the cleanup it reached before it goes to its consumer,
# and a value the conditions refuse is undone, its cleanup's print with it.
# The control is the same function over a class with no override, whose
# call is no dispatch: `Plain` gives 3 then 1, as `derived`'s Vals does.
base := class:
    Vals()<transacts>:int = 4 | 1
derived := class(base):
    Vals<override>()<transacts>:int = 3 | 1
plain := class:
    Plain()<transacts>:int = 3 | 1
Find(B:base)<transacts>:int =
    for (V := B.Vals()):
        defer:
            Print("defer {V}")
        return V | V + 10
    0
Control(B:plain)<transacts>:int =
    for (V := B.Plain()):
        defer:
            Print("defer {V}")
        return V | V + 10
    0
Main()<transacts>:void =
    # 3 then 13, each after the cleanup of the row it is returned in
    for (X := Find(derived{})):
        Print("found {X}")
    # 3 is refused and undone; 13 is taken
    if (V := Find(derived{}), V = 13):
        Print("first {V}")
    # the first value
    if (V := Find(derived{})):
        Print("one {V}")
    # both refused: nothing of either is left
    if (V := Find(derived{}), V = 99):
        Print("wrong {V}")
    else:
        Print("none")
    for (X := Control(plain{})):
        Print("control found {X}")
    if (V := Control(plain{}), V = 13):
        Print("control first {V}")
    if (V := Control(plain{})):
        Print("control one {V}")
    if (V := Control(plain{}), V = 99):
        Print("control wrong {V}")
    else:
        Print("control none")
