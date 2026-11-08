# expect: no class at or below expr can be constructed without an instance of itself
expr(t:type) := class<abstract>:
    Sub:expr(t)
    Eval():t
lit := class(expr(int)):
    N:int
    Eval<override>():int = N
holder(t:type) := class:
    E:expr(t)
Run(H:holder(t) where t:type):t = H.E.Eval()
Main():void = Print("ok")
