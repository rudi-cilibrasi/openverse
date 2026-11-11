Two(N:int):int=N|N+1
Run():int=
    var Total:int=0
    defer:
        set Total+=100
        Print("source {Total}")
    if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),W:=block{defer{set Total+=10;Print("operand cleanup {Total}")};if(A=0)then return Total else 0;0}):
        Print("normal {W}")
    Total
Main():void=Print("result {Run()}")
