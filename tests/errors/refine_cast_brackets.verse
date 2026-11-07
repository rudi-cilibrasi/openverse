# expect: 4:12: a cast to age can fail: write age[X]
age := type{_X:int where 0 <= _X, _X <= 120}
Main():void =
    A := age(5)
