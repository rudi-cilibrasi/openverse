# expect: leaf has more Verse Core type arguments than expr
expr(t:type) := class<abstract>:
    Eval():t
mid(a:type, b:type) := class<abstract>(expr(tuple(a, b))):
    X:int = 0
leaf := class(mid(int, string)):
    Eval<override>():tuple(int, string) = (1, "s")
Main():void = Print("x")
