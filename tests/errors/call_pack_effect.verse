# expect: writes
F(P:tuple(int,int))<writes>:int=P(0)+P(1)
Main()<computes>:void=Print("{F(1,2)}")
