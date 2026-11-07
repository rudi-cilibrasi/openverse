# expect: 5:4: set += on an age needs a cast: write set X = age[X + …], which fails when the result is not one
age := type{_X:int where 0 <= _X, _X <= 120}
Main():void =
    var A:age = 3
    set A += 1
