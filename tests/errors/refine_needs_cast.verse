# expect: 5:4: an int is an age only after a cast: write age[X], which fails when X is not one
age := type{_X:int where 0 <= _X, _X <= 120}
Main():void =
    X:int = 5
    A:age = X
