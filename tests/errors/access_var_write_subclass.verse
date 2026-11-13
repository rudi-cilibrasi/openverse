# expect: Field of base cannot be set here: its var is <private>
# (VarAccessSpecifiers.versetest:116: a class below may read it, not set it)
base := class:
    var<private> Field:int = 42
derived := class(base):
    Reset():void = set Field = 10
Main():void = Print("{derived{}.Field}")
