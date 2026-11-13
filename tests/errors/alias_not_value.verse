# expect: 3:26: maybe is a type alias: a type, not a value
maybe := ?int
F(X:int)<decides>:maybe = maybe[X]
Main():void = {}
