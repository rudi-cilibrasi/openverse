# expect: expected tuple(int, tuple(string, int)), found tuple(int, string, int)
F(P:tuple(int,tuple(string,int))):int=P(0)
Main():void=Print("{F(1,"two",3)}")
