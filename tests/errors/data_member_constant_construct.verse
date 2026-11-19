# expect: the value of the constant Shared constructs thing
# A class without specifiers constructs with the transacts effect, which a
# module's constant does not allow: UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses it, error 3512 "This
# archetype instantiation constructs a class that has the 'transacts'
# effect, which is not allowed by its context"
# (tests/conformance/versevm/followup-3582/div-const-constructor).
thing := class:
    Size:int = 3
Shared:thing = thing{}
Main():void = Print("{Shared.Size}")
