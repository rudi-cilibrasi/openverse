# expect: <converges> is unsupported
# A function of the program's cannot be <converges> (#494): UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses it too, error 3565 "The
# 'converges' effect is only allowed on native functions", so no data member
# can call one of the program's
# (tests/conformance/versevm/followup-3582/div-const-converges).
Count()<converges>:int = 3
Limit:int = Count()
Main():void = Print("{Limit}")
