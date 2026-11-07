# expect: pair has type parameters that base does not have, so it cannot override Get
base(t:type) := class:
    Value:t
    Get():t = Value
pair(t:type, u:type) := class(base(t)):
    Other:u
    Get<override>():t = Value
Main():void = Print("x")
