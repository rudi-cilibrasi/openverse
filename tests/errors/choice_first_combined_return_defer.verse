# expect: return is not allowed in a defer: block
Two(N:int):int=N|N+1
Run():void=
    defer:if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),if(A=0)then return 0 else 0):Print("bad")
Main():void=Run()
