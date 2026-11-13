# expect: F is defined twice with parameters a call cannot tell apart, (int, tuple(int, int)) and (int, tuple(int, int))
# A destructured group is a tuple parameter for overloads too (Book of Verse ch. 6)
F(A:int, (B:int, C:int)):int = 1
F(A:int, P:tuple(int, int)):int = 2
Main():void =
    Print("{F(1, (2, 3))}")
