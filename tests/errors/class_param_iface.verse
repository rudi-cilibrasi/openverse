# expect: box gives named the type arguments none, but its own are t
named := interface:
    Name():string
box(t:type) := class(named):
    Value:t
    Name<override>():string = "box"
Main():void = Print("x")
