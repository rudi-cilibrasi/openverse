# expect: 2:0: the type alias list names itself, so writing it out would never end
list(t:type) := ?tuple(t, list(t))
Main():void = {}
