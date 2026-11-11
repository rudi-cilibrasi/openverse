Two(N:int):int = N|N+1
Pause(N:int)<suspends>:void =
    Sleep(0.01)
    Print("wait {N}")
Use(F:type{_(:int)<suspends>:void})<suspends>:void =
    for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),A=0,B<2):
        F(B)
Main()<suspends>:void = Use(Pause)
