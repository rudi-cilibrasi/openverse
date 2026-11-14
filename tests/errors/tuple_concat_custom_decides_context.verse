# expect: can fail
operator'+'(A:tuple(int,int), B:tuple(int,int))<decides><computes>:int = block{A(0)>0;7}
Main():void = Print("{(1,2)+(3,4)}")
