# Control of generic-higher-order: the generic higher-order functions One
# and Two called with Succ, a function that is not generic. Not a Book case.
# OpenVerse prints
#   one 1 | two 2
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints one 1 | two 2, as OpenVerse
# does.
One(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(X)
Two(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(F(X))
Succ(X:int)<transacts>:int = X + 1

Main():void =
    Print("OVPROBE one {One(Succ, 0)}")
    Print("OVPROBE two {Two(Succ, 0)}")
