# Incomplete tails erase their arms, including recursively returned values.
R(N:int)<computes>:any =
    if(N<=0):return 10|11
    if(N>1)then(N|R(N-2))else if(N=1)then(7|8)
Main():void =
    for(V:=R(2)): Print("tail value")
    for(V:=R(0)): Print("returned value")
