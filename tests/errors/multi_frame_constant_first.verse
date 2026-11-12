# expect: 4:0: F has several values and is recursive, or called by a recursive one, and it is not <computes>
# (a constant read before its call of itself, which would be read after it in a
# return frame, and a constant may run code where it is read: not taken lazily, #283)
F(N:int)<transacts><decides>:int =
    N > 0
    K + F[N - 1] | N
K:int = (Print("k"); 1)
Main()<transacts>:void =
    for (V := F[2]) { Print("{V}") }
