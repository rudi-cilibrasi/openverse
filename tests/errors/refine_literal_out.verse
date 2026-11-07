# expect: 4:4: 150 is not an age: it does not meet its conditions
age := type{_X:int where 0 <= _X, _X <= 120}
Main():void =
    A:age = 150
