# ToString (and so interpolation) of an int beyond 64 bits is a runtime
# error (#724), as on Epic's Verse VM (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, 2026-11-18: the probe
# book-int-interpolate-pow63 prints "big computed", then the session stops
# with ErrRuntime_GeneratedNativeInternal in ToString(:int), "Value exceeds
# the range of a 64 bit integer"). The Book of Verse, ch. 2: integers past
# 64 bits "cannot be used in string interpolation".
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("big computed")
    Print("in range {Big - 1}")
    Print("value {Big}")
    Print("not reached")
