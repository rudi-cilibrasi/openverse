# Control of the 3509 rule (#724): G(3, 4) of G(X:tuple(int, int)), no named
# parameter: the arguments pack into the tuple. OpenVerse prints
#   packed 7
G(X:tuple(int, int)):int = X(0) + X(1)

Main():void =
    Print("OVPROBE packed {G(3, 4)}")
