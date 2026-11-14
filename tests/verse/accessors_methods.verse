# A field with accessors named bare in its class's methods, also in loops.
tally := class:
    var Total<getter(GetTotal)><setter(SetTotal)>:int = external{}
    var Sum:int = 0
    GetTotal(:accessor)<transacts>:int = Sum
    SetTotal(:accessor, V:int)<transacts>:void = set Sum = V
    AddAll(Xs:[]int)<transacts>:int =
        for (X : Xs):
            set Total += X
        Total
    Bump()<transacts>:void =
        Old := Total
        set Total = Old + 1

Main()<transacts>:void =
    T := tally{}
    Print(ToString(T.AddAll(array{1, 2, 3})))
    T.Bump()
    Print(ToString(T.Total))
    Ys := for (I := 1..3) do T.Total + I
    Print(ToString(Ys.Length))
