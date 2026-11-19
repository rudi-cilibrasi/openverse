# expect: 6:15: the value of the constant Limit calls Min, which might not complete
# Of the built-ins, a data member may call only a <converges> one (#724):
# Abs is (the Book's Runtime API reference), Min is not. UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) reports 3582 at Min's arguments only
# (tests/conformance/versevm/followup-3582/div-const-intrinsic).
Limit:int = Min(Abs(-3), 7)
Main():void = Print("{Limit}")
