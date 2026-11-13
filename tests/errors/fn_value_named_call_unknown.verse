# expect: a value of type type{_(:int):int} has no parameter ?Step
# A call through a value names only the parameters its type has, though the function has more (#503)
Inc(X:int, ?Step:int = 1):int = X + Step
Main():void =
    F:type{_(:int):int} = Inc
    Print("{F(1, ?Step := 2)}")
