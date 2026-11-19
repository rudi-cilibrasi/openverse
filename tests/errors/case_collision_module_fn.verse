# expect: have names that differ only in case and take the same parameters
# Two module functions whose names differ only in case, with the same
# parameters (#724): Epic's toolchain maps them to one function. UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses them with error 9200
# (followup-book2/case-collision-module-fn; the Book's Blueprint VM tests,
# Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest:92).
Function():int = 42
FUNCTION():int = 420
Main():void = Print("{Function()} {FUNCTION()}")
