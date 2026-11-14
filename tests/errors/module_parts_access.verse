# expect: the parts of module A have different access levels, internal and <public>
# (the Book of Verse's tests, PartialModuleDefinitions.versetest:163, 3623)
A := module:
    X<public>:int = 1
A<public> := module:
    Y<public>:int = 2
Main():void = {}
