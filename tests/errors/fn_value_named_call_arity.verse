# expect: a value of type type{_(:int, ?Step:int = …):int} takes 1 positional argument(s), found 2
# Named arguments are given by name through a value too (#503)
Inc(X:int, ?Step:int = 1):int = X + Step
Main():void =
    F:type{_(:int, ?Step:int = 0):int} = Inc
    Print("{F(1, 2)}")
