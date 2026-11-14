# expect: expected []int, found int
operator'+'(A:tuple(int,int), B:tuple(int,int))<computes>:int = 7
Main():void =
    A:[]int = (1,2)+(3,4)
    Print("{A.Length}")
