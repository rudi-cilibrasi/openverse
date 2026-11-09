# expect: when a named argument's default has no type of its own
expr(t:type) := class<abstract>:
    Eval():t
    Pick(?Alt:?t = false):t =
        if (A := Alt?) then A else Eval()
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    A:a
    B:b
    Eval<override>():tuple(a, b) = (A, B)
    Pick<override>(?Alt:?tuple(a, b) = false):tuple(a, b) =
        if (X := Alt?) then X else (A, B)
Run2(E:expr(t) where t:type):t = E.Pick()
Main():void =
    P := pairE(int, int){A := 1, B := 2}
    Print("{Run2(P)(1)}")
