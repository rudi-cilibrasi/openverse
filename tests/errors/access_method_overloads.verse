# expect: the overloads of meter.Read must all have one access level
# (a use reaches a method by its name: openverse, as for a module's functions)
meter := class:
    Read<public>(X:int):int = X
    Read<private>(X:string):int = 0
Main():void = {}
