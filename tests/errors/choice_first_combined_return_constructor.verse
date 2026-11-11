# expect: return is not allowed in a constructor
Two(N:int):int=N|N+1
product:=class{N:int=0}
Make<constructor>():=product:
    N:=block{if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),if(A=0)then return 0 else 0):Print("bad");0}
Main():void=Print("{Make().N}")
