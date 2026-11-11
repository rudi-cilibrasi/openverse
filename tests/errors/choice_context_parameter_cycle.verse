# expect: the default of ?N of Run uses itself
Two(N:int):int=N|N+1
Run(?N:int=block{R:=for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2))):Run();R.Length}):int=N
Main():void=Print("{Run()}")
