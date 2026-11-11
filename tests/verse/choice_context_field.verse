Two(N:int):int=N|N+1
box(t:type):=class:
    Value:t
    Count:int=block{R:=for(A0:=(Two(0)|Two(2)),A1:=(Two(0)|Two(2)),A2:=(Two(0)|Two(2)),A3:=(Two(0)|Two(2))):block{E:[]t=Concatenate();E.Length};R.Length}
Make(X:t where t:type):box(t)=box(t){Value:=X}
Main():void=Print("{Make(7).Count}")
