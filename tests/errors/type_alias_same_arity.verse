# expect: 'box' is defined twice (only functions can be overloaded)
# (an alias beside a type of its name at the same number of type
# parameters: a use could name either)
box(t:type) := class:
    X:t
box(u:type) := ?u
Main():void = {}
