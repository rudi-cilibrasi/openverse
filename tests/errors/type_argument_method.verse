# expect: c.M takes a type as an argument (a parameter t:type used as a type): openverse takes types as arguments of functions only, not yet of methods
c := class:
    M(t:type):?t = false
Main():void = {}
