# expect: 'box' is defined twice (only functions can be overloaded, and a type alias beside a type of its name at another number of type parameters)
# (two classes of one name at two numbers of type parameters: openverse
# takes a type alias beside a type, as the Book of Verse's tests write it,
# and keys classes by their names)
box(t:type) := class:
    X:t
box(t:type, u:type) := class:
    Y:u
Main():void = {}
