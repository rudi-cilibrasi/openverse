# Follow-up (#724): a module constant beyond 64 bits computed by a function.
# Epic refuses literal arithmetic (book-int-pow64-module-const, error 9003);
# OpenVerse refuses only that, computes this one at run time and prints
# "above". A 9003 refusal here would mean every module constant is
# evaluated in 64 bits.
Next(N:int)<computes>:int = N + 1
Big:int = Next(9223372036854775807)

Main():void =
    if (Big > 9223372036854775807) then Print("OVPROBE above") else Print("OVPROBE not above")
