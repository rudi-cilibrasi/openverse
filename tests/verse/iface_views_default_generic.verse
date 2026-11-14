# The default of an interface referred to through views (i0, which c4 gives
# []t), called through one below it (i1) from generic code: i1(t)'s classes
# include c2, whose view gives i0 ?char, which i0(?t) is only when t is
# char; each class's test refines by its pins, as Verse Core's are (#526)
i0(p:type) := interface:
    D():string = "d"
    N(X:p):string
i1(p:type) := interface(i0(?p)):
    M(X:p):string
i2(p:type) := interface:
    K(X:p):string
c1(t:type, u:type) := class(i1(t), i2(?u)):
    M<override>(X:t):string = "c1.M"
    N<override>(X:?t):string = "c1.N"
    K<override>(X:?u):string = "c1.K"
c2(t:type) := class(i1(char), i2(?t)):
    M<override>(X:char):string = "c2.M"
    N<override>(X:?char):string = "c2.N"
    K<override>(X:?t):string = "c2.K"
c4(t:type, u:type) := class(i2(u), i0([]t)):
    K<override>(X:u):string = "c4.K"
    N<override>(X:[]t):string = "c4.N"
# (i1 only takes its type parameter in, so an i1(t) gives no t: the type
# is given as an argument, ParametricFunctions.versetest 356)
Read(t:type, X:i1(t)):string = X.D()
Main():void =
    X:i1(string) = c1(string, string){}
    Print(Read(string, X))
    Y:i1(char) = c2(int){}
    Print(Read(char, Y))
