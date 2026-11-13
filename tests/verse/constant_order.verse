# A constant uses constants defined before it in its scope (the Book of Verse's
# tests, DefaultValueAssignment.versetest 95-128): those of another module, or
# of an enclosing scope, it may use wherever they are defined
Base:int = 1
Next:int = Base + 1
limits := module:
    Low<public>:int = Base + 10
    High<public>:int = Low + Top
    Over<public>:int = other.Value * 2
other := module:
    Value<public>:int = 7
Top:int = 100
Main():void =
    Print("{Next} {limits.Low} {limits.High} {limits.Over}")
