# expect: intbox fixes or repeats type arguments that base leaves open, so it cannot override Get
base(t:type) := class:
    Value:t
    Get():t = Value
intbox := class(base(int)):
    Get<override>():int = 0
Main():void = Print("x")
