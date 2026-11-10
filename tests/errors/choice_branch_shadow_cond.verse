# expect: 5:19: 'V' is already defined
Main()<transacts>:void =
    M : ?int = option{3}
    V := 1
    for (Z := (if (V := M?) then (V | 1) else 0)):
        Print("{Z}")
