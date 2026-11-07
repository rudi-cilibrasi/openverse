# expect: 'for{…}' has no body
Main():void =
    Xs := for { X := 1..3 } { X }
