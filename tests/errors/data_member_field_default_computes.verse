# expect: the default of field 'Size' of thing calls Count, which might not complete
# A <computes> function is no <converges> one (#724): UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses its call in a field's
# default, error 3582
# (tests/conformance/versevm/followup-3582/div-field-default-computes).
Count()<computes>:int = 3
thing := class:
    Size:int = Count()
Main():void = Print("{thing{}.Size}")
