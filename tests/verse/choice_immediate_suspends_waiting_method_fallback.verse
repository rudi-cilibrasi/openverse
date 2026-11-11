Two(N:int):int = N|N+1
waiter := class:
    Pause(N:int)<suspends>:void =
        Sleep(0.01)
        Print("wait {N}")
Main()<suspends>:void =
    W:=waiter{}
    for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),A=0,B<2):
        W.Pause(B)
