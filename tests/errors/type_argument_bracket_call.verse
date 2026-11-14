# expect: 6:19: First[…] gives its type argument t in brackets, which openverse does not support yet
# A type given as an argument in a call in brackets is not supported yet:
# said, not read as a value of the type argument's parameter.
First(t:type, Xs:[]t)<decides>:t = Xs[0]
Main():void =
    if (X := First[string, array{"a", "b"}]) then Print(X)
