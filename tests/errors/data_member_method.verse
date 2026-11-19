# expect: the value of the constant Twice calls thing.Double, which might not complete
# A method is the program's, so not <converges> (#724). UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses Shared.Double() in a
# constant, error 3582 (tests/conformance/versevm/followup-3582/div-const-method,
# whose class has no specifiers and so is refused at Shared too, 3512).
thing := class<computes>:
    Size:int = 3
    Double()<computes>:int = Size * 2
Shared:thing = thing{}
Twice:int = Shared.Double()
Main():void = Print("{Twice}")
