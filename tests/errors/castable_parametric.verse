# expect: box has type parameters, so it cannot be <castable>, as thing above it is
thing := class<castable> {}
box(t:type) := class(thing) {}
Main():void = {}
