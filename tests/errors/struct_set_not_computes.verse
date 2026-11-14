# expect: 8:9: set of field 'M' of s: only a <computes> struct's fields are set
# Only a <computes> struct's field is set through a variable (Book of Verse
# ch. 5, "Only structs marked <computes> (pure structs) allow field mutation
# through a variable"; its tests, Mutability.versetest:426).
s := struct{M:int = 0}
Main():void =
    var S:s = s{}
    set S.M = 1
