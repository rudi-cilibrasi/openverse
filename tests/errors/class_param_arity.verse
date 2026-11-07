# expect: base takes 1 type argument(s), found 0
base(t:type) := class:
    Value:t
sub := class(base):
    X:int = 0
Main():void = Print("x")
