# expect: the value of the constant Limit calls Count, which might not complete
# A module's constant may not call a function of the program's (#724): no
# such function is <converges>. UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086)
# refuses it, error 3582 "Divergent calls (calls that might not complete)
# cannot be used to define data-members"
# (tests/conformance/versevm/followup/constant-default-call).
Count():int = 3
Limit:int = Count()
Main():void = Print("{Limit}")
