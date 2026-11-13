# (#283) A recursive function with several values that returns from a branch with a defer: of
# its own: the defer: runs as each of the return's values leaves the branch.
R(N:int)<transacts>:int =
    if(N<=0):
        defer: Print("cleanup")
        return 1|2
    N|R(N-1)
Main():void = for(X:=R(1)): Print("{X}")
