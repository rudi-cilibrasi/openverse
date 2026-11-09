# a class that fixes the type arguments a class between it and expr adds to
# closed types overrides too: the dispatch opens them, and its pins fix them (#209)
expr(t:type) := class<abstract>:
    Eval():t
mid(a:type, b:type) := class<abstract>(expr(tuple(a, b))):
    X:int = 0
leaf := class(mid(int, string)):
    Eval<override>():tuple(int, string) = (1, "s")

Run(E:expr(t) where t:type):t = E.Eval()
Main():void =
    R := Run(leaf{})
    Print("{R(0)} {R(1)}")
