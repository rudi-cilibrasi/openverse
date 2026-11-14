# expect: type other does not satisfy subtype(shape) in a call of Count
shape := class{}
other := class{}
Count(t:subtype(shape), Xs:[]t):int = Xs.Length
Main():void =
    Print(ToString(Count(other, array{other{}})))
