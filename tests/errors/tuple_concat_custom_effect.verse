# expect: calls operator'+'
operator'+'(A:tuple(int,int), B:tuple(int,int))<transacts>:int = 7
Main()<computes>:void = block{N:=(1,2)+(3,4);()}
