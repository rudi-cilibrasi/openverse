# expect: 'Shadowed' is already defined, as a type parameter
box(Shadowed:type) := class:
    F():float =
        (local:)Shadowed:float = 0.0
        (local:)Shadowed
Main():void = {}
