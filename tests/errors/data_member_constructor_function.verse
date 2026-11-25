# expect: the value of the constant Shared calls MakeThing, which might not complete
# A constructor function is the program's, so not <converges> (#724). UEFN
# 43.12 (++Fortnite+Release-43.12-CL-60598086) refuses it, error 3582
# (tests/conformance/versevm/followup-3582/div-const-constructor-fn).
thing := class:
    Size:int = 3
MakeThing<constructor>(N:int) := thing:
    Size := N
Shared:thing = MakeThing(4)
Main():void = Print("{Shared.Size}")
