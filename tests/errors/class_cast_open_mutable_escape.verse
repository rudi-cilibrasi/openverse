# expect: would name what is unknown outside it
expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
Bad(E:expr(t) where t:type):?expr(int) =
    if(Print("prefix"),P:=vpair[E])then option{P.L}else false
Main():void={}
