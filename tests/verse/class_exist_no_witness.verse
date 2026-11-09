# a class with a type parameter of its own and methods but no override
# keeps no value of it, so making one needs none (#209)
lp2(t:type) := class:
    Me:lp2(t)
base(t:type) := class:
    V:t
    Get():t = V
sub(t:type, u:type) := class(base(t)):
    W:?u
    Has():logic = if (W?) then true else false
Main():void =
    S := sub(int, lp2(int)){V := 1, W := false}
    Print("{S.Get()}")
