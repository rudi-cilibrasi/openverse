# refinement types (#136): literals checked at compile time, failable casts, a refined value as its base
age := type{_X:int where 0 <= _X, _X <= 120}
percent := type{_X:float where 0.0 <= _X, _X <= 1.0}
finite := type{_X:float where -Inf < _X, _X < Inf}
Half(X:finite)<computes>:float = X / 2.0
Older(A:age, Years:int):int = A + Years
Describe(A:age):string =
    case (A):
        0 => "newborn"
        _ => "{A} years"
Main():void =
    ValidAge:age = 25
    Print("{ValidAge} {Older(ValidAge, 5)} {Half(100.0)} {Describe(ValidAge)} {Describe(0)}")
    if (not age[150]) then Print("150 is not an age")
    if (not age[-1]) then Print("-1 is not an age")
    UserInput:float = 0.25
    if (Value := percent[UserInput]) then Print("percent {Value}")
    if (not percent[1.5], not finite[1.0 / 0.0], not finite[0.0 / 0.0]) then Print("refused")
    var A:age = 30
    if (B := age[A + 1]) then set A = B
    if (A < 40, A = 31) then Print("{A} compares as an int")
    Ages:[]age = array{1, 2, 3}
    var T:int = 0
    for (X : Ages) { set T += X }
    Print("{T}")
