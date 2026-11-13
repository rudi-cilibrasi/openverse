# expect: an operand of '=' must be comparable, and subtype(c) is a class
c := class{}
F()<decides>:void =
    X:subtype(c) = c
    X = X
Main():void = {}
