# expect: return is not allowed in a parameter's default
Two(N:int):int=N|N+1
Run(?N:int=block{if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),if(A=0)then return 0 else 0):Print("bad");0}):int=N
Main():void=Print("{Run()}")
