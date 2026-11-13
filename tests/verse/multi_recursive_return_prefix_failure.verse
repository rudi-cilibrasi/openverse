# Failure after selecting a returning branch fails the invocation; it never selects else.
# (The return is in tail position, a branch of the body's last if: the function
# is <decides>, Return.versetest:157.)
R(N:int)<transacts><decides>:int =
    Print("visit {N}")
    if(N<=0):
        Print("selected {N}")
        N=0
        Z:=N+10
        return Z|Z+1
    else:
        Print("fall {N}")
        N|R[N-2]
Main():void =
    for(X:=R[1]): Print("got {X}")
    Print("all done")
    if(X:=R[1],X>9)then Print("bad")else Print("none")
    if(X:=R[2],X>9)then Print("first {X}")else Print("bad")
