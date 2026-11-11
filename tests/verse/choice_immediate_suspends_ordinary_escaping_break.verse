Two(N:int):int = N|N+1
Main()<suspends>:void =
    var Total:int=0
    loop:
        for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),if(B=1)then break else 0):
            set Total+=A+B
        Print("bad")
    Print("total {Total}")
