Two(N:int):int=N|N+1
Use(X:t where t:type):void=
    defer:
        R:=for(A0:=(Two(0)|Two(2)),A1:=(Two(0)|Two(2)),A2:=(Two(0)|Two(2)),A3:=(Two(0)|Two(2))):block{E:[]t=Concatenate();E.Length}
        Print("rows {R.Length}")
    Print("start")
Main():void=Use(7)
