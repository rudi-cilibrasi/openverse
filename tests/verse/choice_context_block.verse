Two(N:int):int=N|N+1
box(t:type):=class:
    Value:t
    var Count:int=0
    block:
        R:=for(A0:=(Two(0)|Two(2)),A1:=(Two(0)|Two(2)),A2:=(Two(0)|Two(2)),A3:=(Two(0)|Two(2))):block{E:[]t=Concatenate();E.Length}
        set Count=R.Length
Main():void=Print("{box(int){Value:=7}.Count}")
