# expect: 8:20: the default of field 'Size' of thing calls Count, which might not complete
# A field's default is a data member's definition (#724): UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses a call of a function without
# specifiers there with 3582, not for its no_rollback effect
# (tests/conformance/versevm/followup-3582/div-field-default-call).
Count():int = 3
thing := class:
    Size:int = Count()
Main():void = Print("{thing{}.Size}")
