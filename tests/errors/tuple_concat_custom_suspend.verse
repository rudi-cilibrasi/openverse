# expect: it can only be called in a <suspends> function
operator'+'(A:tuple(int,int), B:tuple(int,int))<suspends>:int = block{Sleep(0.1);7}
Main():void = Print("{(1,2)+(3,4)}")
