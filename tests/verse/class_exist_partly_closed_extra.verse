# a class that fixes one of the type arguments a class above it adds (#209)
expr(t:type) := class<abstract>:
    Eval():t
mid(a:type, b:type) := class<abstract>(expr(tuple(a, b))):
    X:int = 0
leaf2(x:type) := class(mid(x, string)):
    V:x
    Eval<override>():tuple(x, string) = (V, "s")
Main():void =
    Print("{leaf2(int){V := 3}.Eval()(0)}")
