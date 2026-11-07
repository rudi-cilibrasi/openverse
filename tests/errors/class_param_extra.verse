# expect: type parameter u of pair must be one of base's type arguments
base(t:type) := class:
    Value:t
pair(t:type, u:type) := class(base(t)):
    Other:u
Main():void = Print("x")
