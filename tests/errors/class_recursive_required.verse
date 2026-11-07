# expect: class node has a field that needs an instance of node
# A class whose required field is of its own type has no initial value
# for a variable of its type (and no instance can ever be built).
node := class:
    Next:node

Show(N:node):void = Print("x")
Main():void =
    var X:?node = false
    if (N := X?) then Show(N)
