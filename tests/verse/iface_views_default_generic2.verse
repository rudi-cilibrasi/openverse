# The default of an interface referred to through views (i1, which c1 gives
# string through i4 and c0 gives u), called from generic code through an
# interface below it (i4(p, u)): its classes are tested under their pins'
# refinement, not through a temporary of i1(u), which c1's closed view is
# not (#530)
i1(p:type) := interface:
    D():string = "d"
i2(p:type, u:type) := interface:
    K(X:p):string
i4(p:type, u:type) := interface(i1(u)):
    N():int = 0
c0(u:type) := class(i1(u), i2(int, int)):
    K<override>(X:int):string = "c0.K"
c1(t:type) := class(i4([]t, string), i2(string, int)):
    K<override>(X:string):string = "c1.K"
GD(X:i4(p, u) where p:type, u:type):string = X.D()
Main():void =
    X := c1(int){}
    Print(X.D())
    Print(GD(X))
