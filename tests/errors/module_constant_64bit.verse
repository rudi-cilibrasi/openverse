# expect: leaves the 64-bit range when the module is evaluated (integer add overflow
# A module constant is evaluated in 64 bits (#724): Epic's Verse VM build
# (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-18) refuses
# this with error 9003, "Runtime error while evaluating module" (the probe
# book-int-pow64-module-const), though the same arithmetic in a function
# gives 2^64 at run time.
TwoTo64:int = (9223372036854775807 + 1) * 2

Main():void =
    if (TwoTo64 > 0) then Print("unreachable")
