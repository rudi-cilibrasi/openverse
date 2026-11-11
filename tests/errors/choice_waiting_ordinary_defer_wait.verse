# expect: defer cannot suspend
Two(N:int):int=N|N+1
Early(N:int):int=
    if(N<0):return N
    N|N+1
Main()<suspends>:void=
    for(A:=(Two(1)|Two(3)),B:=Early(10)):
        Sleep(0.0)
        defer:Sleep(0.0)
        Print("bad")
