# Control of the 3509 rule (#724): G(3, 4) of G(X:tuple(int, int)), no named
# parameter: the arguments pack into the tuple. OpenVerse prints
#   packed 7
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) admits it (compiled only).
G(X:tuple(int, int)):int = X(0) + X(1)

Main():void =
    Print("OVPROBE packed {G(3, 4)}")
