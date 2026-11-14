# expect: the parts of module M give it different @available attributes
# (the Book of Verse's tests, Attributes/available.versetest 337-368: "some
# but not all modules have available", 3552)
M<public> := module:
    A<public>:int = 42
@available{MinUploadedAtFNVersion := 3000}
M<public> := module:
    B<public>:int = 43
Main():void = {}
