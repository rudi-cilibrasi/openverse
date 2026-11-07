# expect: parametric classes cannot implement interfaces yet
named := interface:
    Name():string
box(t:type) := class(named):
    Value:t
    Name<override>():string = "box"
Main():void = Print("x")
