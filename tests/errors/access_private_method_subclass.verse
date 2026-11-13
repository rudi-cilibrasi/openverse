# expect: Check of base is <private>: only base's own code may use it
# (Classes/AccessSpecifiers.versetest:73: a class below does not see a <private> method)
base := class:
    Check<private>():int = 1
derived := class(base):
    Use():int = Check()
Main():void = Print("{derived{}.Use()}")
