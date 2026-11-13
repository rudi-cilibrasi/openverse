Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return 0
    N|N+1
Run()<suspends>:void=
    R:[][]int=for(A:=(Two(1)|Two(3)),B:=Early(10),C:=(Two(20)|Two(22)),D:=Early(30)):
        Sleep(0.01)
        Empty:[]int=array{}
        Empty
    Print("empty rank {R.Length}")
    for(Row:R):
        if(Row.Length<>0):Err()
Main()<suspends>:void=Run()
