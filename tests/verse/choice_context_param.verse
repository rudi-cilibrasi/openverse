Two(N:int):int=N|N+1
Use(X:t,?N:int=block{R:=for(A0:=(Two(0)|Two(2)),A1:=(Two(0)|Two(2)),A2:=(Two(0)|Two(2)),A3:=(Two(0)|Two(2))):block{E:[]t=Concatenate();E.Length};R.Length} where t:type):int=N
Main():void=Print("{Use(7)}")
