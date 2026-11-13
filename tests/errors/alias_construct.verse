# expect: 4:19: maybe is a type alias of a type that is not a struct or a class: it cannot be constructed
maybe := ?int
Main():void =
    X:maybe = maybe{}
