# expect: class expr has no field 'V'
expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
other:=class(expr(int)){Eval<override>():int=42}
Bad(E:expr(t) where t:type):?t =
    if(Print("prefix"),P:=vpair[E],L:=lit[P.L],set P.L=other{},R:=lit[P.R])then option{(P.L.V,R.V)}else false
Main():void={}
