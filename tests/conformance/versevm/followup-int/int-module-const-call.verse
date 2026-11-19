# Follow-up (#724): a module constant beyond 64 bits computed by a function.
# OpenVerse computes it at run time and prints "above". Epic refuses it at
# compile time, 3582: "Divergent calls (calls that might not complete) cannot
# be used to define data-members" (Next is <computes>), a rule OpenVerse does
# not have yet; whether the value fits in 64 bits is not reached.
Next(N:int)<computes>:int = N + 1
Big:int = Next(9223372036854775807)

Main():void =
    if (Big > 9223372036854775807) then Print("OVPROBE above") else Print("OVPROBE not above")
