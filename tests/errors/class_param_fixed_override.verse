# expect: intbox fixes or repeats the type arguments of base, so it cannot override Get
base(t:type) := class:
    Value:t
    Get():t = Value
intbox := class(base(int)):
    Get<override>():int = 0
Main():void = Print("x")
