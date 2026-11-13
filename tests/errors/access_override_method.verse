# expect: <public> on Area<override>: an override has the access of the member it overrides and writes none
# (Book of Verse tests, AccessLevelInheritance.versetest:711: error 3650)
shape := class:
    Area<protected>():int = 0
square := class(shape):
    Area<public><override>():int = 4
Main():void = {}
