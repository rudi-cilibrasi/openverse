Two(N:int):int = N|N+1
Main()<suspends>:void =
    E:=event(int){}
    branch:
        V:=E.Await()
        Print("event {V}")
    for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),A=0,B<2):
        E.Signal(B)
        Print("signal {B}")
    Sleep(0.01)
