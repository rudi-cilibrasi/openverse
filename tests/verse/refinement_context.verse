# refined literals take their type from context; refined values in indices, Floor, as rationals (#136 review)
age := type{_X:int where 0 <= _X, _X <= 120}
Six():age =
    Print("hi")
    6
Pick(C:logic):age = case (C):
    true => 5
    _ => 6
Main():void =
    C:logic = true
    A:age = if (C?) then 5 else 6
    O:?age = option{5}
    T:tuple(age, int) = (5, 1)
    X:int = 500
    D:age = age[X] or 7
    Xs:[]int = array{10, 20, 30, 40, 50, 60}
    R:rational = A
    if (V := Xs[A], O2 := O?) then Print("{A} {O2} {T(0)} {D} {Six()} {Pick(false)} {V} {Floor(A)}")
    if (R = 5) then Print("rational")
