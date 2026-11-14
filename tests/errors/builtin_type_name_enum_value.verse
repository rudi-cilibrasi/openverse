# expect: 4:0: 'int' is the name of a built-in type: a value of the enum kind takes it only qualified, (kind:)int
# Unqualified, an enum's value named like a built-in type collides with it
# (Book of Verse ch. 9: "Enumerators can collide with identifiers in parent scopes").
kind := enum:
    int
    other
Main():void = {}
