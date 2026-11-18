# Book: Tests/ParametricTypes.versetest:222 (verse_vm_only, assert_valid): a
# parametric class whose field is t->t, made with a function of two ints.
my_type(t:type) := class:
    F:t->t
F1(FLocal:t->t where t:type)<transacts>:my_type(t) = my_type(t){F := FLocal}
F2(X:int)<computes>:int = X + 1
F3()<transacts><decides>:void =
    C := F1(F2)
    C.F(0) = 1
F4(X:int, Y:int)<computes>:tuple(int, int) = (Y, X)
F5()<transacts><decides>:void =
    C := F1(F4)
    C.F(1, 2)

Main():void =
    if (F3[]):
        Print("OVPROBE F3 succeeded")
    else:
        Print("OVPROBE F3 failed")
    if (F5[]):
        Print("OVPROBE F5 succeeded")
    else:
        Print("OVPROBE F5 failed")
