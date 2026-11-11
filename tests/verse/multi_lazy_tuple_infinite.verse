Grow(N:int,S:string)<computes>:string = S | Grow((N+1,S+"x"))
Main():void =
    if(V:=Grow(0,""),V.Length>3)then Print(V)
    O:=option{V:=Grow(0,"a");V.Length=3;V}
    if(V:=O?)then Print(V)
