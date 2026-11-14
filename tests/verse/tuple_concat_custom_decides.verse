operator'+'(A:tuple(int,int), B:tuple(int,int))<decides><computes>:int =
    A(0)>0
    A(1)*100+B(0)*10+B(1)
Main():void =
    if (N := (1,2)+(3,4)) then Print("custom {N}")
