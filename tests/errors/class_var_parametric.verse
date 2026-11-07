# expect: a parametric class is a value, so its fields cannot change
box(t:type) := class:
    var Value:t

Main():void = Print("x")
