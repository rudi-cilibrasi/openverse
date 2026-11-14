# expect: field 'A' of c3 has no default value and must be given
# the inherited default is not kept (Book of Verse tests,
# Attributes/override.versetest 37-47: "Object archetype must initialize data
# member", 3600)
c2 := class:
    A:int = 2
c3 := class(c2):
    A<override>:int
Main():void = Print("{c3{}.A}")
