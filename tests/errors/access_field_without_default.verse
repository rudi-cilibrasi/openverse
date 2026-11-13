# expect: the field Code of badge has no default, so a construction gives it one, but it is internal to the top level where badge's constructor is wider
# (Classes/AccessSpecifiers.versetest:412: a field with no default is at least as visible as the constructor)
badge<public> := class:
    Code:int
Main():void = {}
