Two(N:int):int = N|N+1
Use()<suspends>:int =
    var Total:int=0
    defer: Print("cleanup {Total}")
    for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2))):
        set Total+=A+B
        if(B=1)then return Total
    -1
Main()<suspends>:void = Print("result {Use()}")
