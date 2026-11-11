# expect: branch cannot be in a loop or for body
Two(N:int):int=N|N+1
Early(N:int):int=
    if(N<0):return N
    N|N+1
Main()<suspends>:void=
    for(A:=(Two(1)|Two(3)),B:=Early(10)):
        Sleep(0.0)
        branch:Print("bad")
